# == Schema Information
#
# Table name: members
#
#  id         :integer          not null, primary key
#  name       :string(255)
#  party_id   :integer
#  created_at :datetime
#  updated_at :datetime
#

class Member < ActiveRecord::Base
  belongs_to :party

  validates :party, presence: true
  validates :name, presence: true, uniqueness: true
end
