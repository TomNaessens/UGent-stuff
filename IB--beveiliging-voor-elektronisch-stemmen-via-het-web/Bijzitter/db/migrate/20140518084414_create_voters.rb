class CreateVoters < ActiveRecord::Migration
  def change
    create_table :voters do |t|

      t.string :true_identity
      t.string :anonymous_identity
      t.string :key
      t.boolean :voted, default: false

      t.timestamps

      t.index :anonymous_identity
    end
  end
end
