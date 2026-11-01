#!/usr/bin/ruby
# -*- coding: utf-8 -*-

require "fileutils"
require "json"
require "logger"
require "optparse"
require "time"
require "thread"
require "tmpdir"
require "uri"

require "faraday"
require "faraday/multipart"
require "websocket-client-simple"
require "tomlrb"
require "nokogiri"
require "sqlite3"

module IPCSolver
  class MastodonClient
    STATE_INITIAL = 0
    STATE_COMPLETED = 1
    POLL_PERIOD = 3 * 60
    # Number of trailing lines of the solver/LaTeX log included in error logs
    LOG_TAIL_LINES = 40

    attr_reader :poll_queue, :config_file, :logger

    def initialize(config_file: "mastodon-config.toml", keep_scratch: false)
      @config_file = File.expand_path(config_file)
      @keep_scratch = keep_scratch
      @logger = Logger.new($stderr, progname: "mastodon", level: ENV["LOG_LEVEL"] || Logger::INFO)
    end

    def start
      validate_config
      logger.info "Using config #{config_file}, state directory #{state_dir}"
      @myself = get_myself
      logger.info "Logged in as @#{@myself["acct"]} on #{domain}"
      @poll_queue = Thread::Queue.new
      periodic_poller = nil
      watcher = nil
      SQLite3::Database.new(File.join(state_dir, "mastodon.sqlite3")) do |db|
        setup_database(db)
        periodic_poller = Thread.start do
          run_periodic_poller
        end
        watcher = create_watcher
        logger.info "Start polling..."
        while event = @poll_queue.pop
          logger.debug "Checking mentions (cause: #{event[:type]})"
          poll_mentions(db)
          poll_requests(db)
        end
      end
    rescue Exception => e
      logger.fatal "Terminating due to #{format_exception(e)}" unless e.is_a?(Interrupt)
      raise
    ensure
      watcher&.close
      periodic_poller&.raise Interrupt
      periodic_poller&.join
    end

    def run_periodic_poller
      loop do
        @poll_queue.push({ type: :periodic })
        sleep POLL_PERIOD
      end
    rescue Interrupt
      # OK
    end

    def create_watcher
      query = URI.encode_www_form({
        access_token: access_token,
        stream: "user:notification"
      })
      this = self
      ws = WebSocket::Client::Simple.connect("wss://#{domain}/api/v1/streaming?#{query}") do |ws|
        ws.on :open do
          this.logger.info "WebSocket connected"
        end
        ws.on :close do |e|
          this.logger.warn "WebSocket closed#{e ? ": #{e.inspect}" : ""}"
        end
        ws.on :message do |msg|
          case msg.type
          when :ping
            ws.send("", type: :pong)
          when :text
            this.poll_queue&.push({ type: :streaming })
          end
        end
        ws.on :error do |e|
          this.logger.error "WebSocket error: #{this.format_exception(e)}"
        end
      end
      ws
    end

    def poll_mentions(db)
      last_read = get_last_read(db)
      new_last_read = last_read
      mentions_after = Time.now - 24 * 60 * 60
      mention_stream.each do |m|
        time = Time.iso8601(m["created_at"])
        new_last_read = [new_last_read, time].compact.max
        break if last_read && time < last_read

        process_mention(db, m)
      end
      set_last_read(db, new_last_read) if new_last_read
    end

    def process_mention(db, m)
      html = m["status"]["content"]
      status_id = m["status"]["id"]
      requester = m["account"]["acct"]
      if m["account"]["bot"]
        logger.debug "Ignoring mention #{status_id} from bot @#{requester}"
        return
      end

      text = Nokogiri::HTML::DocumentFragment.parse(html).text
      if create_request(db, status_id: status_id, text: text, requester: requester)
        logger.info "New request #{status_id} from @#{requester}: #{text.inspect}"
      end
    end

    def poll_requests(db)
      pending = get_pending_requests(db)
      pending.each do |req|
        has_reply = get_status_context(req.status_id)["descendants"].any? do |child|
          child["account"]["id"] == @myself["id"]
        end
        if has_reply
          logger.info "Skipping #{req.status_id}: already replied"
        else
          process_request(req)
        end
        req.state_cd = STATE_COMPLETED
        update_request_state(db, req)
      end
    end

    def process_request(req)
      logger.info "Responding to #{req.status_id}..."
      tid = req.status_id
      prop = req.text.dup
      prop.sub!(/\A@\w+(@[\-\w.]+)?/, "")
      prop.gsub!(/\A\s+/m, "")

      with_scratch_dir(tid) do |scratch_dir|
        File.open(File.join(scratch_dir, "#{tid}-prop.txt"), "w") do|t|
          t.write prop
        end

        command = ["bash", File.join(__dir__, "mastodon-make-image.sh"), scratch_dir, "#{tid}"]

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
        result = "@#{req.requester} #{result}"
        if media
          media_obj = create_media(
            Faraday::Multipart::FilePart.new(
              media,
              'image/png'
            )
          )
        end
        status = create_status(
          result,
          media: media_obj ? [media_obj] : nil,
          idempotency_key: "result-#{tid}",
          in_reply_to_id: req.status_id
        )
        logger.info "Replied to #{tid} with #{status["id"]}: #{result.inspect}"
      end
    rescue StandardError => e
      logger.error "Failed to respond to #{req.status_id}: #{format_exception(e)}"
      raise
    end

    # Collects the input, the exit status, and the outputs of
    # mastodon-make-image.sh, for diagnosing failures.
    def solver_failure_details(scratch_dir, tid, status)
      details = +"  exit status: #{status.inspect}\n"
      ["#{tid}-prop.txt", "#{tid}.out", "#{tid}.log"].each do |name|
        path = File.join(scratch_dir, name)
        content =
          if File.exist?(path)
            lines = File.read(path).scrub.lines
            omitted = lines.size > LOG_TAIL_LINES ? "  (#{lines.size - LOG_TAIL_LINES} lines omitted)\n" : ""
            omitted + lines.last(LOG_TAIL_LINES).map { |l| "    #{l.chomp}\n" }.join
          else
            "    (missing)\n"
          end
        details << "  #{name}:\n#{content}"
      end
      details
    end

    def format_exception(e)
      message = "#{e.class}: #{e.message}"
      # Faraday errors carry the response from the server
      if e.respond_to?(:response) && e.response.is_a?(Hash)
        message << " (HTTP #{e.response[:status]}: #{e.response[:body].to_s[0, 1000]})"
      end
      message << "\n" << (e.backtrace || []).map { |bt| "    #{bt}" }.join("\n")
    end

    def config
      @config ||= Tomlrb.load_file(config_file)
    end

    # Directory holding persistent state (mastodon.sqlite3): the first entry of
    # $STATE_DIRECTORY (set by systemd's StateDirectory=), or $PWD.
    def state_dir
      @state_dir ||= File.expand_path(ENV["STATE_DIRECTORY"].to_s.split(":").first || ".")
    end

    # Yields a fresh temporary directory, removed afterwards unless
    # --keep-scratch is given.
    def with_scratch_dir(name)
      dir = Dir.mktmpdir("ipc_solver-mastodon-#{name}-")
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

    def create_media(file)
      client.post("/api/v2/media", { file: file }).body
    end

    def create_status(text, media:, idempotency_key:, in_reply_to_id:)
      params = {
        status: text,
        media_ids: (media || []).map { |m| m["id"] },
        in_reply_to_id: in_reply_to_id
      }
      client.post("/api/v1/statuses", **params) do |req|
        req.headers["Idempotency-Key"] = idempotency_key
      end.body
    end

    def mention_stream
      enum_for(:each_mentions)
    end

    def each_mentions
      opts = { types: ["mention"] }
      loop do
        notifications = client.get("/api/v1/notifications", opts).body
        break if notifications.empty?

        notifications.each do |notification|
          yield notification
        end
        opts[:max_id] = notifications.last["id"]
      end
    end

    def get_myself
      client.get("/api/v1/accounts/verify_credentials").body
    end

    def get_status_context(id)
      client.get("/api/v1/statuses/#{id}/context").body
    end

    def client
      base_url = "https://#{domain}"
      token = access_token
      @client ||= Faraday.new(base_url) do |conn|
        conn.request :authorization, 'Bearer', access_token
        conn.request :multipart
        conn.request :url_encoded
        conn.response :json
        conn.response :raise_error
      end
    end

    def validate_config
      domain
      client_key
      client_secret
      access_token
    end

    def domain
      config.dig("app", "domain") || (raise "No domain configured")
    end

    # Not used for now; kept so that the app credentials can be stored alongside.
    def client_key
      secret("app", "client_key", required: false)
    end

    # Not used for now; kept so that the app credentials can be stored alongside.
    def client_secret
      secret("app", "client_secret", required: false)
    end

    def access_token
      secret("user", "access_token")
    end

    # Reads a secret either from the config file or from the environment
    # variable MASTODON_<KEY>, but not both. Empty values are treated as unset.
    def secret(section, key, required: true)
      env_name = "MASTODON_#{key.upcase}"
      config_value = config.dig(section, key)
      config_value = nil if config_value == ""
      env_value = ENV[env_name]
      env_value = nil if env_value == ""
      if config_value && env_value
        raise "#{key} is configured both in #{config_file} and in #{env_name}; use only one"
      end
      value = config_value || env_value
      if required && !value
        raise "No #{key} configured (set #{section}.#{key} in #{config_file} or #{env_name})"
      end
      value
    end

    def setup_database(db)
      db.execute_batch <<~SQL
        CREATE TABLE IF NOT EXISTS requests (
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          status_id TEXT NOT NULL UNIQUE,
          state_cd INTEGER NOT NULL DEFAULT 0,
          text TEXT,
          requester TEXT
        );

        CREATE INDEX IF NOT EXISTS index_pending_requests
        ON requests (id)
        WHERE state_cd = 0;

        CREATE TABLE IF NOT EXISTS last_reads (
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          name TEXT NOT NULL UNIQUE,
          last_read TEXT NOT NULL
        );
      SQL
    end

    def create_request(db, status_id:, text:, requester:)
      db.execute(<<~SQL, [status_id, text, requester])
        INSERT INTO requests (status_id, text, requester)
        VALUES (?, ?, ?)
        ON CONFLICT (status_id) DO NOTHING;
      SQL
      db.changes > 0
    end

    Request = Struct.new(:id, :status_id, :state_cd, :text, :requester)

    def get_pending_requests(db)
      requests = []
      db.execute(<<~SQL) do |row|
        SELECT id, status_id, state_cd, text, requester FROM requests
        WHERE state_cd = 0;
      SQL
        requests << Request.new(*row)
      end
      requests
    end

    def update_request_state(db, req)
      db.execute(<<~SQL, [req.state_cd, req.id])
        UPDATE requests
        SET state_cd = ?
        WHERE id = ?;
      SQL
    end

    def get_last_read(db)
      db.execute <<~SQL do |row|
        SELECT last_read FROM last_reads
        WHERE name = 'mentions';
      SQL
        return Time.iso8601(row[0])
      end
      nil
    end

    def set_last_read(db, last_read)
      db.execute(<<~SQL, [last_read.iso8601, last_read.iso8601])
        INSERT INTO last_reads (name, last_read)
        VALUES ('mentions', ?)
        ON CONFLICT (name) DO
          UPDATE
          SET last_read = ?
          WHERE name = 'mentions';
      SQL
    end
  end
end

options = {}
OptionParser.new do |opts|
  opts.banner = "Usage: #{$0} [options]"
  opts.on("-c", "--config FILE", "Config file (default: ./mastodon-config.toml)") do |v|
    options[:config_file] = v
  end
  opts.on("--keep-scratch", "Do not remove per-request scratch directories") do
    options[:keep_scratch] = true
  end
end.parse!
IPCSolver::MastodonClient.new(**options).start
