class CreateParties < ActiveRecord::Migration
  def change
    create_table :parties do |t|
      t.string :name
      t.integer :votes, default: 0

      t.timestamps
    end
  end
end
