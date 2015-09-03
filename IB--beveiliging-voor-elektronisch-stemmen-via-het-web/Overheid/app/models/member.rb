# == Schema Information
#
# Table name: members
#
#  id         :integer          not null, primary key
#  name       :string(255)
#  votes      :integer          default(0)
#  party_id   :integer
#  created_at :datetime
#  updated_at :datetime
#

class Member < ActiveRecord::Base
  belongs_to :party
end
