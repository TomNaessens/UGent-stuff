# This file should contain all the record creation needed to seed the database with its default values.
# The data can then be loaded with the rake db:seed (or created alongside the db with db:setup).

Party.create([{ name: "Fire" }, { name: "Water" }])

Member.create({ name: "Charmander", party: Party.all.first })
Member.create({ name: "Magmar", party: Party.all.first })
Member.create({ name: "Ponita", party: Party.all.first })

Member.create({ name: "Squirtle", party: Party.all.second })
Member.create({ name: "Poliwag", party: Party.all.second })
Member.create({ name: "Seaking", party: Party.all.second })
