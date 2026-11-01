#!/usr/bin/ruby
# -*- coding: utf-8 -*-

require "fileutils"
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

# Yields a fresh temporary directory, removed afterwards unless
# --keep-scratch is given.
def with_scratch_dir(name)
  dir = Dir.mktmpdir("ipc_solver-twitter-#{name}-")
  yield dir
ensure
  if dir
    if $keep_scratch
      puts "Scratch directory kept: #{dir}"
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

def crush_error(sleep_length=0, &block)
  block.call()
rescue
  message = "[#{Time.now}] #{$!.class}: #{$!.message}\n"
  $!.backtrace.each do|bt|
    message << "        #{bt}\n"
  end
  print message
  File.open(File.join($state_dir, "twitter-log.txt"), "a") do|file|
    file.print message
  end
  sleep(sleep_length)
end

def process_tweet(target)
  target.text.start_with?('@' + $self_screen_name) or return
  crush_error(90) do
    p ["processing", target.id]
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
          result = "An error occured."
        end
        if File.exist?(File.join(scratch_dir, "#{tid}1.png"))
          media = File.join(scratch_dir, "#{tid}1.png")
        end
      else
        result = "An error occured"
      end
      result = ".@#{target.user.screen_name} #{result} (#{rand(36**5).to_s(36)})"
      tw_option = {
        :in_reply_to_status_id => target.id
      }
      if media
        $twitter_client.update_with_media(result, File.new(media), tw_option)
      else
        $twitter_client.update(result, tw_option)
      end
    end
    p ["done",target.id]
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

loop do
  crush_error do
    p ["polling mentions"]
    mt = $twitter_client.mentions_timeline
    while process_tweets(mt) do
    end
  end
  sleep 60
end

