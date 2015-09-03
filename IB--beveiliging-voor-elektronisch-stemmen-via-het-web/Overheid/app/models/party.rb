# == Schema Information
#
# Table name: parties
#
#  id         :integer          not null, primary key
#  name       :string(255)
#  votes      :integer          default(0)
#  created_at :datetime
#  updated_at :datetime
#

class Party < ActiveRecord::Base
  has_many :members
end
