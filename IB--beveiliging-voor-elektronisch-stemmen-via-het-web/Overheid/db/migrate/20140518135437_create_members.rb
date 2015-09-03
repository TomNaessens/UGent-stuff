class CreateMembers < ActiveRecord::Migration
  def change
    create_table :members do |t|
      t.string :name
      t.integer :votes, default: 0
      t.references :party

      t.timestamps
    end
  end
end
