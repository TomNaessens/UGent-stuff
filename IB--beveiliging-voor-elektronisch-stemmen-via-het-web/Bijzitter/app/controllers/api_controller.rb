class ApiController < ApplicationController
  before_filter :set_default_response_format

  def letter
    post_data = JSON.parse params[:request]

    key = SecureRandom.hex(32)
    id = SecureRandom.hex(32)

    v = Voter.find_by_true_identity post_data['identity']

    if v.nil?
      Voter.create(true_identity: post_data['identity'], anonymous_identity: id, key: key, voted: false)
    else
      if v.voted
        res = { error: "You have already voted." }
      else
        v.anonymous_identity = id
        v.key = key
        v.save
      end
    end

    res ||= {
      key: key,
      id: id,
      choices: {
        Party.all.first.name => Party.all.first.members.pluck(:name),
        Party.all.second.name => Party.all.second.members.pluck(:name),
      }
    }

    respond_to do |format|
      format.json { render json: res }
    end

  end

  def key
    post_data = params[:request]

    v = Voter.find_by_anonymous_identity post_data['id']

    if v.nil?
      res = { error: "Voter not found" }
    elsif v.voted
      res = { error: "Voter has already voted" }
    else
      res = { key: v.key }
    end

    respond_to do |format|
      format.json { render json: res }
    end
  end

  def confirm
    post_data = params[:request]

    v = Voter.find_by_anonymous_identity post_data['id']

    if v.nil?
      res = { error: "Voter not found" }
    elsif v.voted
      res = { error: "Voter has already voted" }
    else
      res = { success: "Voter voted" }
      v.voted = true
      v.save
    end

    respond_to do |format|
      format.json { render json: res }
    end
  end

  def check
    post_data = JSON.parse params[:request]

    key = OpenSSL::PKey::RSA.new(File.read("#{Dir.home}/ssl/bijzitter.key"))

    v = Voter.find_by_anonymous_identity post_data['anonymous_identity']
    if !v.nil? and v.voted
      msg = "Meneer/Mevrouw #{v.true_identity} heeft gestemd."
    else
      msg = "Meneer/Mevrouw heeft NIET gestemd."
    end

    digest = OpenSSL::Digest::SHA256.new

    sign = key.sign digest, msg
    res = {
      brief: msg,
      sign: sign.unpack("H*").first
    }

    respond_to do |format|
      format.json { render json: res }
    end
  end

  private

  def set_default_response_format
    request.format = :json
  end
end
