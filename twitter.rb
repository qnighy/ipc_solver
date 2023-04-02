#!/usr/bin/ruby
# -*- coding: utf-8 -*-

require "pstore"
require "twitter"
load "./twitter-config.rb"

`test -d workdir || mkdir workdir`

$dblock = Mutex.new
$db = PStore.new("twitter-db")

def crush_error(sleep_length=0, &block)
  block.call()
rescue
  message = "[#{Time.now}] #{$!.class}: #{$!.message}\n"
  $!.backtrace.each do|bt|
    message << "        #{bt}\n"
  end
  print message
  File.open("twitter-log.txt", "a") do|file|
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

    File.open("workdir/#{tid}-prop.txt", "w") do|t|
      t.write prop
    end

    command = ["bash", "./twitter-make-image.sh", "#{tid}"]

    result = nil
    media = nil
    if system(command.join(" "))
      result = File.read("workdir/#{tid}.out").strip
      if result == ""
        result = "An error occured."
      end
      if File.exists?("workdir/#{tid}1.png")
        media = "workdir/#{tid}1.png"
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

