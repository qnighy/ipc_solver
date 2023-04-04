#!/usr/bin/ruby
# -*- coding: utf-8 -*-

require "fileutils"
require "json"
require "time"
require "thread"
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

    attr_reader :poll_queue

    def start
      @myself = get_myself
      @poll_queue = Thread::Queue.new
      periodic_poller = nil
      watcher = nil
      FileUtils.mkdir_p("workdir_mastodon")
      SQLite3::Database.new("mastodon.sqlite3") do |db|
        setup_database(db)
        periodic_poller = Thread.start do
          run_periodic_poller
        end
        watcher = create_watcher
        $stderr.puts "Start polling..."
        while event = @poll_queue.pop
          $stderr.puts "Checking mentions (cause: #{event[:type]})"
          poll_mentions(db)
          poll_requests(db)
        end
      end
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
        ws.on :message do |msg|
          case msg.type
          when :ping
            ws.send("", type: :pong)
          when :text
            this.poll_queue&.push({ type: :streaming })
          end
        end
        ws.on :error do |e|
          $stderr.puts "WebSocket error: #{e.inspect} / #{e.backtrace}"
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
      return if m["account"]["bot"]

      text = Nokogiri::HTML::DocumentFragment.parse(html).text
      create_request(db, status_id: status_id, text: text, requester: requester)
    end

    def poll_requests(db)
      pending = get_pending_requests(db)
      pending.each do |req|
        has_reply = get_status_context(req.status_id)["descendants"].any? do |child|
          child["account"]["id"] == @myself["id"]
        end
        process_request(req) unless has_reply
        req.state_cd = STATE_COMPLETED
        update_request_state(db, req)
      end
    end

    def process_request(req)
      $stderr.puts "Responding to #{req.status_id}..."
      tid = req.status_id
      prop = req.text.dup
      prop.sub!(/\A@\w+(@[\-\w.]+)?/, "")
      prop.gsub!(/\A\s+/m, "")

      File.open("workdir_mastodon/#{tid}-prop.txt", "w") do|t|
        t.write prop
      end

      command = ["bash", "./mastodon-make-image.sh", "#{tid}"]

      result = nil
      media = nil
      if system(command.join(" "))
        result = File.read("workdir_mastodon/#{tid}.out").strip
        if result == ""
          result = "An error occured."
        end
        if File.exist?("workdir_mastodon/#{tid}1.png")
          media = "workdir_mastodon/#{tid}1.png"
        end
      else
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
      create_status(
        result,
        media: media_obj ? [media_obj] : nil,
        idempotency_key: "result-#{tid}",
        in_reply_to_id: req.status_id
      )
    end

    def config
      @config ||= Tomlrb.load_file("mastodon-config.toml")
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

    def domain
      config["app"]["domain"] || (raise "No domain configured")
    end

    def client_key
      config["app"]["client_key"] || (raise "No client_key configured")
    end

    def client_secret
      config["app"]["client_secret"] || (raise "No client_secret configured")
    end

    def access_token
      config["user"]["access_token"] || (raise "No access_token configured")
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

IPCSolver::MastodonClient.new.start
