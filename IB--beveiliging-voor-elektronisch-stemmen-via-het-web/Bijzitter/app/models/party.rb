# == Schema Information
#
# Table name: parties
#
#  id         :integer          not null, primary key
#  name       :string(255)
#  created_at :datetime
#  updated_at :datetime
#

class Party < ActiveRecord::Base
  has_many :members

  validates :name, presence: true, uniqueness: true
end
