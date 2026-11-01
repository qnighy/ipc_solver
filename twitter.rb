#!/usr/bin/ruby
# -*- coding: utf-8 -*-

require "fileutils"
require "logger"
require "optparse"
require "pstore"
require "tmpdir"
require "twitter"

$config_file = nil
$keep_scratch = false
OptionParser.new do |opts|
  opts.banner = "Usage: #{$0} [options]"
  opts.on("-c", "--config FILE", "Config file (default: ./twitter-config.rb if it exists)") do |v|
    $config_file = File.expand_path(v)
  end
  opts.on("--keep-scratch", "Do not remove per-request scratch directories") do
    $keep_scratch = true
  end
end.parse!

# The default config file is optional; an explicitly given one is not.
if $config_file
  load $config_file
else
  $config_file = File.expand_path("twitter-config.rb")
  load $config_file if File.exist?($config_file)
end

# Persistent state (twitter-db, twitter-log.txt): the first entry of
# $STATE_DIRECTORY (set by systemd's StateDirectory=), or $PWD.
$state_dir = File.expand_path(ENV["STATE_DIRECTORY"].to_s.split(":").first || ".")

$logger = Logger.new($stderr, progname: "twitter", level: ENV["LOG_LEVEL"] || Logger::INFO)
# Errors are additionally recorded in twitter-log.txt
$error_logger = Logger.new(File.join($state_dir, "twitter-log.txt"), progname: "twitter", level: Logger::WARN)

def log(severity, message)
  $logger.add(severity, message)
  $error_logger.add(severity, message)
end

# Number of trailing lines of the solver/LaTeX log included in error logs
LOG_TAIL_LINES = 40

# Yields a fresh temporary directory, removed afterwards unless
# --keep-scratch is given.
def with_scratch_dir(name)
  dir = Dir.mktmpdir("ipc_solver-twitter-#{name}-")
  yield dir
ensure
  if dir
    if $keep_scratch
      $logger.info "Scratch directory kept: #{dir}"
    else
      FileUtils.remove_entry(dir)
    end
  end
end

# Reads a secret either from the config file or from the environment
# variable TWITTER_<KEY>, but not both. Empty values are treated as unset.
def load_secret(config, key)
  env_name = "TWITTER_#{key.upcase}"
  config_value = config[key]
  config_value = nil if config_value == ""
  env_value = ENV[env_name]
  env_value = nil if env_value == ""
  if config_value && env_value
    raise "#{key} is configured both in #{$config_file} and in #{env_name}; use only one"
  end
  config_value || env_value || (raise "No #{key} configured (set it in #{$config_file} or #{env_name})")
end

$twitter_config = [
  :consumer_key,
  :consumer_secret,
  :access_token,
  :access_token_secret,
].to_h {|key| [key, load_secret($twitter_config || {}, key)] }

$dblock = Mutex.new
$db = PStore.new(File.join($state_dir, "twitter-db"))

def format_exception(e)
  message = "#{e.class}: #{e.message}"
  # Twitter::Error carries the API error code and the rate limit
  if e.is_a?(Twitter::Error)
    message << " (code #{e.code.inspect}"
    message << ", rate limit resets at #{e.rate_limit.reset_at}" if e.rate_limit&.reset_at
    message << ")"
  end
  message << "\n" << (e.backtrace || []).map { |bt| "    #{bt}" }.join("\n")
end

def crush_error(sleep_length=0, &block)
  block.call()
rescue => e
  log(Logger::ERROR, format_exception(e))
  sleep(sleep_length)
end

# Collects the input, the exit status, and the outputs of
# twitter-make-image.sh, for diagnosing failures.
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

def process_tweet(target)
  target.text.start_with?('@' + $self_screen_name) or return
  crush_error(90) do
    $logger.info "Processing #{target.id} from @#{target.user.screen_name}: #{target.text.inspect}"
    tid = target.id
    prop = target.text.dup
    prop.sub!('@' + $self_screen_name, "")
    prop.gsub!(/^\s+/m,"")
    prop.gsub!("&lt;","<")
    prop.gsub!("&gt;",">")
    prop.gsub!("&amp;","&")

    with_scratch_dir(tid) do |scratch_dir|
      File.open(File.join(scratch_dir, "#{tid}-prop.txt"), "w") do|t|
        t.write prop
      end

      command = ["bash", File.join(__dir__, "twitter-make-image.sh"), scratch_dir, "#{tid}"]

      result = nil
      media = nil
      if system(*command)
        result = File.read(File.join(scratch_dir, "#{tid}.out")).strip
        if result == ""
          log(Logger::ERROR, "Solver produced no output for #{tid}\n#{solver_failure_details(scratch_dir, tid, $?)}")
          result = "An error occured."
        end
        if File.exist?(File.join(scratch_dir, "#{tid}1.png"))
          media = File.join(scratch_dir, "#{tid}1.png")
        else
          log(Logger::WARN, "No image generated for #{tid}")
        end
      else
        log(Logger::ERROR, "#{command.join(" ")} failed for #{tid}\n#{solver_failure_details(scratch_dir, tid, $?)}")
        result = "An error occured"
      end
      result = ".@#{target.user.screen_name} #{result} (#{rand(36**5).to_s(36)})"
      tw_option = {
        :in_reply_to_status_id => target.id
      }
      tweet =
        if media
          $twitter_client.update_with_media(result, File.new(media), tw_option)
        else
          $twitter_client.update(result, tw_option)
        end
      $logger.info "Replied to #{tid} with #{tweet.id}: #{result.inspect}"
    end
  end
end

def process_tweets(tweets)
  success = false
  crush_error do
    $dblock.synchronize do
      $db.transaction do
        target = nil
        $db["read"] ||= {}
        target = tweets.sort_by {|tw|
          tw.created_at
        }.find {|tw|
          !$db["read"][tw.id]
        }
        if target
          $db["read"][target.id] = {}
          process_tweet(target)
          sleep 10
          success = true
        end
      end
    end
  end
  return success
end

$twitter_client = Twitter::REST::Client.new($twitter_config)

$self_userid = $twitter_client.user.id
$self_screen_name = $twitter_client.user.screen_name
$logger.info "Logged in as @#{$self_screen_name}; state directory #{$state_dir}"

loop do
  crush_error do
    $logger.debug "Polling mentions"
    mt = $twitter_client.mentions_timeline
    while process_tweets(mt) do
    end
  end
  sleep 60
end

