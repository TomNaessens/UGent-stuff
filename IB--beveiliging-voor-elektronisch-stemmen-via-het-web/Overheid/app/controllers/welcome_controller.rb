class WelcomeController < ApplicationController
  def index
    @members = Member.all.order('votes desc')
    @parties = Party.all.order('votes desc')
  end

  def clear
    Member.all.each do |m|
      m.votes = 0
      m.save
    end
    Party.all.each do |p|
      p.votes = 0
      p.save
    end

    redirect_to :index
  end
end
