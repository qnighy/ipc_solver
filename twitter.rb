#!/usr/bin/ruby
# -*- coding: utf-8 -*-

require "pstore"
require "twitter"
load "./twitter-config.rb"

`test -d workdir || mkdir workdir`

$db = PStore.new("twitter-db")

def process_tweet(target)
  begin
    p ["processing", target.id]
    tid = target.id
    prop = target.text.dup
    prop.gsub!(/@[a-zA-Z0-9_]+/,"")
    prop.gsub!(/^[.]/,"")
    prop.gsub!("&lt;","<")
    prop.gsub!("&gt;",">")
    prop.gsub!("&amp;","&")
    File.open("workdir/#{tid}-prop.txt", "w") do|t|
      t.write prop
    end
    result = nil
    media = nil
    if prop.match(/[pP]roblem|PROBLEM|問題|もんだい/)
      result = `./ipc_solver --generate`
    else
      if system("bash ./twitter-make-image.sh #{tid}")
        tex = File.read("workdir/#{tid}.tex")
        if tex.include?("%provable")
          if File.exists?("workdir/#{tid}1.png")
            result = "Provable"
            media = "workdir/#{tid}1.png"
          else
            result = "image generation failed"
          end
        elsif tex.include?("%unprovable")
          result = "Unprovable"
        elsif tex.include?("%parse_error")
          result = "Parse Error"
        else
          result = "Determination failed"
        end
      else
        result = "An error occured"
      end
    end
    result = "@#{target.user.screen_name} #{result} (#{rand(36**5).to_s(36)})"
    tw_option = {
      :in_reply_to_status_id => target.id
    }
    if media
    $twitter_client.update_with_media(result, File.new(media), tw_option)
    else
    $twitter_client.update(result, tw_option)
    end
    p ["done",target.id]
  rescue
    p $!
    File.open("twitter-log.txt", "a") do|file|
      file.puts $!.inspect
    end
    sleep 90
  end
end

def process_tweets(tweets)
  success = false
  begin
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
  rescue
    p $!
    File.open("twitter-log.txt", "a") do|file|
      file.puts $!.inspect
    end
  end
  return success
end

$twitter_client = Twitter::REST::Client.new($twitter_config)
$twitter_client_strm = Twitter::Streaming::Client.new($twitter_config)

$self_userid = $twitter_client.user.id

Thread.new do
  $twitter_client_strm.user(:replies => "all") do|status|
    p ["processing UserStream"]
    case status
    when Twitter::Tweet
      if status.in_reply_to_user_id == $self_userid
        Thread.new do
          process_tweets([status])
        end
      end
    end
  end
end

loop do
  begin
    p ["polling mentions"]
    mt = $twitter_client.mentions_timeline
    while process_tweets(mt) do
    end
  rescue
    p $!
    File.open("twitter-log.txt", "a") do|file|
      file.puts $!.inspect
    end
  ensure
    sleep 60
  end
end

