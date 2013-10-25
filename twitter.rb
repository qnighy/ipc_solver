#!/usr/bin/ruby
# -*- coding: utf-8 -*-

require "pstore"
require "twitter"
load "./twitter-config.rb"

db = PStore.new("twitter-db")

# Twitter.update_with_media("test 2", File.new("test.png"))

# p Twitter.mentions_timeline

`test -d workdir || mkdir workdir`

loop do
  mt = Twitter.mentions_timeline
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
  prop = target.text
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
  result = "@#{target.user.screen_name} #{result} (#{rand(36**5).to_s(36)})"
  tw_option = {
    :in_reply_to_status_id => target.id
  }
  begin
    if media
      Twitter.update_with_media(result, File.new(media), tw_option)
    else
      Twitter.update(result, tw_option)
    end
  rescue
    p $!
  end
  p ["done",target.id]
  sleep 90
end

