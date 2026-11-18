#!/usr/bin/ruby
# -*- coding: utf-8 -*-

require "cgi/escape"
require "fileutils"
require "logger"
require "optparse"
require "time"
require "tmpdir"

require "sqlite3"
require "tomlrb"
require "x"

module IPCSolver
  # Replies to mentions on X, polling GET /2/users/:id/mentions.
  #
  # Data handling:
  # - Mentions older than max_age are ignored, both on fetching and on processing.
  # - The text of a post is kept in the database only until its request is
  #   handled, and each row is deleted once its expires_at (the post's creation
  #   time plus retention) passes. Usernames are neither fetched nor stored.
  # - Unless redaction is disabled, logs contain post and user IDs, but neither
  #   post text, nor anything derived from it, nor usernames.
  class XBot
    STATE_PENDING = 0
    STATE_IN_PROGRESS = 1
    STATE_COMPLETED = 2
    STATE_FAILED = 3

    DEFAULT_MAX_AGE = 60 * 60
    DEFAULT_RETENTION = 2 * 60 * 60
    DEFAULT_POLL_INTERVAL = 60

    # Number of trailing lines of the solver/LaTeX log included in error logs
    # (only when redaction is disabled)
    LOG_TAIL_LINES = 40

    # Leading @mentions of a post, which include those X adds to a reply
    LEADING_MENTIONS = /\A(?:\s*@\w+)+/

    attr_reader :config_file, :logger

    def initialize(config_file: nil, keep_scratch: false, redact: nil)
      # The default config file is optional; an explicitly given one is not.
      @config_file = File.expand_path(config_file || "x-config.toml")
      @config_required = !config_file.nil?
      @keep_scratch = keep_scratch
      @redact_override = redact
      @logger = Logger.new($stderr, progname: "x", level: ENV["LOG_LEVEL"] || Logger::INFO)
    end

    def start
      validate_config
      logger.info "Using config #{config_file}#{File.exist?(config_file) ? "" : " (absent)"}, state directory #{state_dir}"
      logger.info "max_age=#{max_age}s, retention=#{retention}s, poll_interval=#{poll_interval}s, redact=#{redact?}"
      logger.warn "Scratch directories are kept; they contain post text" if @keep_scratch
      me = client.get("users/me")["data"]
      @my_id = me["id"]
      # Our own username is not user data of others; it is needed to recognize mentions.
      @my_username = me["username"]
      logger.info "Logged in as @#{@my_username} (#{@my_id})"
      SQLite3::Database.new(File.join(state_dir, "x.sqlite3")) do |db|
        setup_database(db)
        abandon_in_progress_requests(db)
        logger.info "Start polling..."
        loop do
          wait = poll_interval
          begin
            purge_expired(db)
            poll_mentions(db)
            process_pending_requests(db)
          rescue X::TooManyRequests => e
            reset_in = e.reset_in || 0
            logger.warn "Rate limited; retrying in #{reset_in}s: #{format_exception(e, backtrace: false)}"
            wait = [wait, reset_in + 1].max
          rescue StandardError => e
            logger.error "Polling failed: #{format_exception(e)}"
          end
          sleep wait
        end
      end
    rescue Exception => e
      logger.fatal "Terminating due to #{format_exception(e)}" unless e.is_a?(Interrupt)
      raise
    end

    # Fetches new mentions and records them as pending requests.
    def poll_mentions(db)
      threshold = Time.now - max_age
      params = {
        "max_results" => 100,
        "tweet.fields" => "created_at,author_id",
      }
      since_id = get_since_id(db, threshold)
      if since_id
        params["since_id"] = since_id
      else
        params["start_time"] = threshold.utc.iso8601
      end

      newest_id = nil
      mentions = []
      loop do
        logger.debug "Fetching mentions (#{params.except("tweet.fields").inspect})"
        res = client.get("users/#{@my_id}/mentions", params:)
        meta = res["meta"] || {}
        newest_id ||= meta["newest_id"]
        mentions.concat(res["data"] || [])
        break unless meta["next_token"]

        params["pagination_token"] = meta["next_token"]
      end

      # Oldest first
      mentions.reverse_each do |m|
        record_mention(db, m, threshold)
      end
      # Saved even when unchanged, to record that it is still current.
      new_since_id = newest_id || since_id
      set_since_id(db, new_since_id) if new_since_id
    end

    def record_mention(db, m, threshold)
      post_id = m["id"]
      created_at = Time.iso8601(m["created_at"])
      if m["author_id"] == @my_id
        logger.debug "Ignoring #{post_id}: our own post"
        return
      end
      if created_at < threshold
        logger.debug "Ignoring #{post_id}: older than max_age (#{created_at.iso8601})"
        return
      end
      text = CGI.unescapeHTML(m["text"])
      prop = extract_proposition(text)
      unless prop
        logger.debug "Ignoring #{post_id}: not addressed to us"
        return
      end
      if create_request(db, post_id:, text: prop, created_at:)
        logger.info "New request #{post_id} from user #{m["author_id"]}: #{redact(prop)}"
      end
    end

    # Returns the text following the leading @mentions, or nil if those do not
    # include us (e.g. we are mentioned only in the middle, or it is a repost).
    def extract_proposition(text)
      mentions = text[LEADING_MENTIONS] or return nil
      names = mentions.scan(/@(\w+)/).flatten.map(&:downcase)
      return nil unless names.include?(@my_username.downcase)

      text.delete_prefix(mentions).lstrip
    end

    def process_pending_requests(db)
      get_pending_requests(db).each do |req|
        update_request_state(db, req.post_id, STATE_IN_PROGRESS)
        state = STATE_FAILED
        begin
          process_request(req)
          state = STATE_COMPLETED
        rescue X::TooManyRequests
          # Nothing has been posted; try again later.
          state = STATE_PENDING
          raise
        rescue StandardError => e
          logger.error "Failed to respond to #{req.post_id}: #{format_exception(e)}"
        ensure
          update_request_state(db, req.post_id, state)
        end
      end
    end

    def process_request(req)
      logger.info "Responding to #{req.post_id}..."
      tid = req.post_id
      with_scratch_dir(tid) do |scratch_dir|
        File.write(File.join(scratch_dir, "#{tid}-prop.txt"), req.text)

        command = ["bash", File.join(__dir__, "x-make-image.sh"), scratch_dir, "#{tid}"]

        result = nil
        media = nil
        if system(*command)
          result = File.read(File.join(scratch_dir, "#{tid}.out")).strip
          if result == ""
            logger.error "Solver produced no output for #{tid}\n#{solver_failure_details(scratch_dir, tid, $?)}"
            result = "An error occured."
          end
          if File.exist?(File.join(scratch_dir, "#{tid}1.png"))
            media = File.join(scratch_dir, "#{tid}1.png")
          else
            logger.warn "No image generated for #{tid}"
          end
        else
          logger.error "#{command.join(" ")} failed for #{tid}\n#{solver_failure_details(scratch_dir, tid, $?)}"
          result = "An error occured"
        end
        # X rejects duplicate posts; make each reply unique.
        result = "#{result} (#{rand(36**5).to_s(36)})"

        body = {
          text: result,
          reply: { in_reply_to_tweet_id: tid },
        }
        if media
          uploaded = client.upload_media(media, media_category: "tweet_image")
          body[:media] = { media_ids: [uploaded.id.to_s] }
        end
        post = client.post("tweets", body)
        # The reply carries no user content, so it is logged unredacted.
        logger.info "Replied to #{tid} with #{post["data"]["id"]}: #{result.inspect}"
      end
    end

    # Collects the exit status and the outputs of x-make-image.sh, for
    # diagnosing failures. All of the files are derived from the post, so only
    # their sizes are reported when redacting.
    def solver_failure_details(scratch_dir, tid, status)
      details = +"  exit status: #{status.inspect}\n"
      ["#{tid}-prop.txt", "#{tid}.out", "#{tid}.log"].each do |name|
        path = File.join(scratch_dir, name)
        content =
          if !File.exist?(path)
            "    (missing)\n"
          elsif redact?
            "    (#{File.read(path).scrub.lines.size} lines, redacted)\n"
          else
            lines = File.read(path).scrub.lines
            omitted = lines.size > LOG_TAIL_LINES ? "  (#{lines.size - LOG_TAIL_LINES} lines omitted)\n" : ""
            omitted + lines.last(LOG_TAIL_LINES).map { |l| "    #{l.chomp}\n" }.join
          end
        details << "  #{name}:\n#{content}"
      end
      details
    end

    # Renders text originating from a post for logging.
    def redact(text)
      redact? ? "[redacted, #{text.length} chars]" : text.inspect
    end

    def format_exception(e, backtrace: true)
      message = "#{e.class}: #{e.message}"
      message << " (HTTP #{e.status})" if e.is_a?(X::HTTPError)
      message << "\n" << (e.backtrace || []).map { |bt| "    #{bt}" }.join("\n") if backtrace
      message
    end

    def config
      @config ||=
        if @config_required || File.exist?(config_file)
          Tomlrb.load_file(config_file)
        else
          {}
        end
    end

    # Directory holding persistent state (x.sqlite3): the first entry of
    # $STATE_DIRECTORY (set by systemd's StateDirectory=), or $PWD.
    def state_dir
      @state_dir ||= File.expand_path(ENV["STATE_DIRECTORY"].to_s.split(":").first || ".")
    end

    # Yields a fresh temporary directory, removed afterwards unless
    # --keep-scratch is given.
    def with_scratch_dir(name)
      dir = Dir.mktmpdir("ipc_solver-x-#{name}-")
      yield dir
    ensure
      if dir
        if @keep_scratch
          logger.info "Scratch directory kept: #{dir}"
        else
          FileUtils.remove_entry(dir)
        end
      end
    end

    def client
      @client ||= X::Client.new(
        api_key: secret("api_key"),
        api_key_secret: secret("api_key_secret"),
        access_token: secret("access_token"),
        access_token_secret: secret("access_token_secret"),
      )
    end

    def validate_config
      %w[api_key api_key_secret access_token access_token_secret].each { |key| secret(key) }
      max_age
      poll_interval
      redact?
      if retention < max_age
        raise "bot.retention (#{retention}) must not be shorter than bot.max_age (#{max_age})"
      end
    end

    def max_age = duration("max_age", DEFAULT_MAX_AGE)
    def retention = duration("retention", DEFAULT_RETENTION)
    def poll_interval = duration("poll_interval", DEFAULT_POLL_INTERVAL)

    def redact?
      return @redact_override unless @redact_override.nil?

      value = config.dig("log", "redact")
      return true if value.nil?
      raise "log.redact must be a boolean" unless value == true || value == false

      value
    end

    # Reads a duration in seconds from the [bot] section.
    def duration(key, default)
      value = config.dig("bot", key)
      return default if value.nil?
      raise "bot.#{key} must be a positive integer (seconds)" unless value.is_a?(Integer) && value > 0

      value
    end

    # Reads a secret either from the [auth] section of the config file or from
    # the environment variable X_<KEY>, but not both. Empty values are treated
    # as unset.
    def secret(key)
      env_name = "X_#{key.upcase}"
      config_value = config.dig("auth", key)
      config_value = nil if config_value == ""
      env_value = ENV[env_name]
      env_value = nil if env_value == ""
      if config_value && env_value
        raise "#{key} is configured both in #{config_file} and in #{env_name}; use only one"
      end
      config_value || env_value || (raise "No #{key} configured (set auth.#{key} in #{config_file} or #{env_name})")
    end

    def setup_database(db)
      db.execute_batch <<~SQL
        CREATE TABLE IF NOT EXISTS requests (
          post_id TEXT PRIMARY KEY,
          state_cd INTEGER NOT NULL DEFAULT 0,
          -- The proposition; set to NULL once the request is handled
          text TEXT,
          created_at TEXT NOT NULL,
          expires_at TEXT NOT NULL
        );

        CREATE INDEX IF NOT EXISTS index_requests_expires_at
        ON requests (expires_at);

        CREATE TABLE IF NOT EXISTS cursors (
          name TEXT PRIMARY KEY,
          value TEXT NOT NULL,
          updated_at TEXT NOT NULL
        );
      SQL
    end

    # A request left in progress may or may not have been replied to; mark it
    # failed rather than risk replying twice.
    def abandon_in_progress_requests(db)
      db.execute(<<~SQL, [STATE_FAILED, STATE_IN_PROGRESS])
        UPDATE requests SET state_cd = ?, text = NULL WHERE state_cd = ?;
      SQL
      logger.warn "Abandoned #{db.changes} request(s) interrupted while in progress" if db.changes > 0
    end

    def purge_expired(db)
      db.execute("DELETE FROM requests WHERE expires_at < ?;", [Time.now.utc.iso8601])
      logger.debug "Purged #{db.changes} expired request(s)" if db.changes > 0
    end

    def create_request(db, post_id:, text:, created_at:)
      db.execute(<<~SQL, [post_id, text, created_at.utc.iso8601, (created_at + retention).utc.iso8601])
        INSERT INTO requests (post_id, text, created_at, expires_at)
        VALUES (?, ?, ?, ?)
        ON CONFLICT (post_id) DO NOTHING;
      SQL
      db.changes > 0
    end

    Request = Struct.new(:post_id, :text)

    def get_pending_requests(db)
      db.execute(<<~SQL, [STATE_PENDING]).map { |row| Request.new(*row) }
        SELECT post_id, text FROM requests
        WHERE state_cd = ?
        ORDER BY created_at;
      SQL
    end

    def update_request_state(db, post_id, state)
      if state == STATE_COMPLETED || state == STATE_FAILED
        db.execute("UPDATE requests SET state_cd = ?, text = NULL WHERE post_id = ?;", [state, post_id])
      else
        db.execute("UPDATE requests SET state_cd = ? WHERE post_id = ?;", [state, post_id])
      end
    end

    # The since_id of the last poll, unless it was saved before the threshold,
    # in which case fetching from it could return many mentions to be ignored.
    def get_since_id(db, threshold)
      row = db.get_first_row("SELECT value, updated_at FROM cursors WHERE name = 'mentions';")
      return nil unless row
      return nil if Time.iso8601(row[1]) < threshold

      row[0]
    end

    def set_since_id(db, since_id)
      db.execute(<<~SQL, [since_id, Time.now.utc.iso8601])
        INSERT INTO cursors (name, value, updated_at)
        VALUES ('mentions', ?, ?)
        ON CONFLICT (name) DO UPDATE
        SET value = excluded.value, updated_at = excluded.updated_at;
      SQL
    end
  end
end

options = {}
OptionParser.new do |opts|
  opts.banner = "Usage: #{$0} [options]"
  opts.on("-c", "--config FILE", "Config file (default: ./x-config.toml if it exists)") do |v|
    options[:config_file] = v
  end
  opts.on("--keep-scratch", "Do not remove per-request scratch directories (they contain post text)") do
    options[:keep_scratch] = true
  end
  opts.on("--[no-]redact", "Redact post text from logs (default: log.redact in the config, or true)") do |v|
    options[:redact] = v
  end
end.parse!
IPCSolver::XBot.new(**options).start
