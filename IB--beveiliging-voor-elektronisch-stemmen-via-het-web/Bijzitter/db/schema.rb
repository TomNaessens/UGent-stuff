# encoding: UTF-8
# This file is auto-generated from the current state of the database. Instead
# of editing this file, please use the migrations feature of Active Record to
# incrementally modify your database, and then regenerate this schema definition.
#
# Note that this schema.rb definition is the authoritative source for your
# database schema. If you need to create the application database on another
# system, you should be using db:schema:load, not running all the migrations
# from scratch. The latter is a flawed and unsustainable approach (the more migrations
# you'll amass, the slower it'll run and the greater likelihood for issues).
#
# It's strongly recommended that you check this file into your version control system.

ActiveRecord::Schema.define(version: 20140518153729) do

  create_table "members", force: true do |t|
    t.string   "name"
    t.integer  "party_id"
    t.datetime "created_at"
    t.datetime "updated_at"
  end

  create_table "nonces", force: true do |t|
    t.string   "nonce"
    t.datetime "created_at"
    t.datetime "updated_at"
  end

  add_index "nonces", ["nonce"], name: "index_nonces_on_nonce"

  create_table "parties", force: true do |t|
    t.string   "name"
    t.datetime "created_at"
    t.datetime "updated_at"
  end

  create_table "sessions", force: true do |t|
    t.string   "session_id", null: false
    t.text     "data"
    t.datetime "created_at"
    t.datetime "updated_at"
  end

  add_index "sessions", ["session_id"], name: "index_sessions_on_session_id", unique: true
  add_index "sessions", ["updated_at"], name: "index_sessions_on_updated_at"

  create_table "voters", force: true do |t|
    t.string   "true_identity"
    t.string   "anonymous_identity"
    t.string   "key"
    t.boolean  "voted",              default: false
    t.datetime "created_at"
    t.datetime "updated_at"
  end

  add_index "voters", ["anonymous_identity"], name: "index_voters_on_anonymous_identity"

end
