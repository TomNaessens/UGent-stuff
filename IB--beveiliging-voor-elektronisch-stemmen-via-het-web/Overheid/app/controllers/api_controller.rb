require 'openssl'

class ApiController < ApplicationController

  before_filter :set_default_response_format

  def stem
    post_data = JSON.parse params[:request]


    # Get key from bijzitter
    body = {
      :query => { :request => { :id => post_data['id'] } },
      :headers => {'Content-Type' => 'application/json'},
      :verify => false
    }
    resp = HTTParty.post("https://zeus.ugent.be/bijzitter/key", body)

    response = JSON.parse resp.body

    if response.has_key? 'error'
      res = response
      logger.debug "Error! #{res}"
    else
      key = response['key']
      iv = post_data['iv']
      ciphertext = post_data['ciphertext']

      de_cipher = OpenSSL::Cipher::Cipher.new("AES-256-CBC")
      de_cipher.padding = 0
      de_cipher.decrypt
      de_cipher.key = [key].pack('H*')
      de_cipher.iv = [iv].pack('H*')

      decoded = de_cipher.update([ciphertext].pack('H*')) << de_cipher.final

      if decoded
        parsed_decoded = JSON.parse decoded

        if parsed_decoded.has_key? 'party' and parsed_decoded.has_key? 'prefs'
          party = Party.find_by_name parsed_decoded['party']
          if !party.nil?
            party.votes = party.votes + 1
            party.save
          end
          prefs = parsed_decoded['prefs']
          if !prefs.nil?
            prefs.each do |p|
              member = Member.find_by_name p
              if !member.nil?
                member.votes = member.votes + 1
                member.save
              end
            end
          end

          # Confirm the vote
          res = HTTParty.post("https://zeus.ugent.be/bijzitter/confirm", body)
        else
          res = { error: "Invalid data" }
        end
      else
        res = { error: "Invalid data" }
      end
    end

    respond_to do |format|
      format.json { render json: res }
    end
  end

  private

  def set_default_response_format
    request.format = :json
  end
end
