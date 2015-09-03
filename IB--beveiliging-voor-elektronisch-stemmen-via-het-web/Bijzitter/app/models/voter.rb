# == Schema Information
#
# Table name: voters
#
#  id                 :integer          not null, primary key
#  true_identity      :string(255)
#  anonymous_identity :string(255)
#  key                :string(255)
#  voted              :boolean          default(FALSE)
#  created_at         :datetime
#  updated_at         :datetime
#

class Voter < ActiveRecord::Base
end
