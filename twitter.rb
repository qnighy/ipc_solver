#!/usr/bin/ruby
# -*- coding: utf-8 -*-

require "pstore"
require "twitter"
load "./twitter-config.rb"

db = PStore.new("twitter-db")

twitter_client = Twitter::REST::Client.new($twitter_config)

# twitter_client.update_with_media("test 2", File.new("test.png"))

# p twitter_client.mentions_timeline

`test -d workdir || mkdir workdir`

loop do
  begin
    mt = twitter_client.mentions_timeline
    target = nil
    db.transaction do
      db["read"] ||= {}
      target = mt.sort_by {|tw|
        tw.created_at
      }.find {|tw|
        !db["read"][tw.id]
      }
      if target
        db["read"][target.id] = {}
      end
    end
    if !target
      p ["polling mentions"]
      sleep 60
      next
    end
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
    twitter_client.update_with_media(result, File.new(media), tw_option)
    else
    twitter_client.update(result, tw_option)
    end
    p ["done",target.id]
    sleep 90
  rescue
    p $!
    File.open("twitter-log.txt", "a") do|file|
      file.puts $!.inspect
    end
    sleep 90
  end
end

