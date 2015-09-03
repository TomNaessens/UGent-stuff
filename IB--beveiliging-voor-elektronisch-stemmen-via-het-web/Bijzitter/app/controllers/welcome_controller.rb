class WelcomeController < ApplicationController
  def index
  end

  def clear
    Voter.destroy_all

    redirect_to :index
  end
end
