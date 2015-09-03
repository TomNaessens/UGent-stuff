#!/usr/bin/python

import sys
import string
from random import choice, randint
from datetime import date

# Config
max_bebras_id_size = 16

# Lees lijst van voor- en achternamen in
lastnames = open("data/achternamen").read().splitlines()
firstnames = open("data/voornamen").read().splitlines()

# Lees lijst met domein-namen in
domains = open("data/domeinen").read().splitlines()

#Lijst met klassenamen
classes = open("data/klassen").read().splitlines()

genders = ['M', 'V']
languages = ['NL', 'FR', 'DE', 'EN']
ages = list(range(10, 19))

levels = {
  "10-12":{'min_age':10, 'max_age':12}, 
  "12-14":{'min_age':12, 'max_age':14},
  "14-16":{'min_age':14, 'max_age':16},
  "16-19":{'min_age':16, 'max_age':19}
}

current_year = date.today().year
#min_date = date(current_year - ages[-1], 1, 1).toordinal()
#max_date = date(current_year - ages[0], 1, 1).toordinal()

# Sets van reeds gegenereerde zaken
generated_emails = set()
generated_ids = set()

next_class_id = 1
next_school_id = 1

# Fancy printing met tabs...
def printTabbed(*args):
  for i in range(1, len(args)):
    print(("{}\t".format(args[i-1])), end=' ')
  print((args[i]))

def printYamlList(list, tabs=4):
  for el in list:
    print(" " * tabs + "- *" + el)

def printYaml(some_name, some_id, tabs=0, **data):
  print("\t" * tabs + "- &" + some_id + " !!" + some_name)
  for k, v in data.items():
    print("\t" * tabs, end=' ')
    print(" ", end=' ')
    print((k + ":").ljust(16), end=' ')
    if isinstance(v, list):
      print("")
      printYamlList(v)
    else:
      print(v)
  print("")

########################
# Generation functions
########################
# Genereert bebras id op basis van naam
def generateBebrasId(firstname, lastname):
  id = firstname[:1].lower() + lastname.lower()
  id = [c for c in id if c in string.ascii_lowercase]
  id = id[:max_bebras_id_size]
  return id

# Genereert geboortedatum op basis van leeftijd
def generateBirthday(min_age, max_age):
  if min_age == 0 or max_age == 0:
    min_age = randint(10, 42)
    max_age = randint(min_age, 42)

  min_date = date(current_year - max_age, 1, 1).toordinal()
  max_date = date(current_year - min_age + 1, 1, 1).toordinal()
  
  return date.fromordinal(randint(min_date, max_date))

# Genereert email op basis van voor- en achternaam
def generateEmail(firstname, lastname):
  name = firstname.lower() + lastname.lower()
  name = [c for c in name if c in string.ascii_lowercase]
  domain = choice(domains)

  return name + '@' + domain

# Genereert random password
def generatePassword():
  len = randint(8, 16)
  return ''.join(choice(string.letters + string.digits) for _ in range(1,len))

# Maakt een random persoon aan
def generatePerson(min_age, max_age):
  firstname = choice(firstnames).capitalize()
  lastname = choice(lastnames).capitalize()

  email = generateEmail(firstname, lastname)
  if email != "NULL" and email in generated_emails:
    return generatePerson()

  bebras_id = generateBebrasId(firstname, lastname)
  if bebras_id in generated_ids:
    return generatePerson()

  generated_emails.add(email)
  generated_ids.add(bebras_id)
  password = generatePassword()

  gender = choice(genders)
  language = choice(languages)
  birthday = generateBirthday(min_age, max_age)

  return firstname, lastname, email, bebras_id, password, gender, language, birthday

# Generate a pupil for a given class and a given age
def generatePupil(class_id, min_age, max_age):
  firstname, lastname, email, bebras_id, password, gender, language, birthday = generatePerson(min_age, max_age)

  # email can be NULL for pupil..
  if randint(1, 100) % 3 == 0:
    email = "NULL"

  return "*"+class_id, (firstname, lastname, email, bebras_id, password, gender, language, birthday)

# Genereert een teacher op basis van een class id
def generateTeacher(class_id):
  return "*"+class_id, generatePerson(23, 42)

def generateClass(num_pupils):
  # TODO: teacher toevoegen
  global next_class_id
  id = next_class_id
  next_class_id = next_class_id + 1

  name = str(randint(1,7)) + choice(classes)
  level = choice(list(levels.keys()))

  min_age = levels[level]['min_age']
  max_age = levels[level]['max_age']

  pupils = []

  for i in range(0, num_pupils):
    pupils.append(generatePupil(name, min_age, max_age))

  return id, name, level, pupils

def generateSchool(num_classes):
  # TODO: School name, adress en tel. nr.
  global next_school_id
  id = next_school_id
  next_school_id = next_school_id + 1

  school_name = "Universiteit Gent"
  country = "Belgie"
  city = "Gent"
  street = "blablastraat 1"
  number = "09 000 00 00"
  
  classes = [generateClass(randint(0, 20)) for _ in range(0, num_classes)]
  
  return id, school_name, (country, city, street, number), classes

def printUsage():
  print(sys.argv[0], "person", "number")
  print(sys.argv[0], "class" , "number")
  print(sys.argv[0], "school", "number")

def main(type, number):

  if type == "person":
    for i in range(0, number):
      firstname, lastname, email, bebras_id, password, gender, language, birthday = generatePerson(0, 0)
      printYaml("models.Pupil", bebras_id,
        firstName=firstname, lastName=lastname, 
        email=email, bebrasId=bebras_id, password=password, 
        gender=gender, language=language, birthday=birthday)
  elif type == "class":
    for i in range(0, number):
      class_id, class_name, class_level, pupils = generateClass(randint(0,20))
      class_yaml_id = "class" + str(class_id)
      pupil_ids = []

      for pupil in pupils:
        _, (fn, ln, email, bebras_id, password, gender, lang, birth) = pupil
        printYaml("models.Pupil", bebras_id,
          firstName=fn, lastName=ln, email=email,
          bebrasId=bebras_id, password=password, gender=gender,
          language=lang, birthday=birth)
  
        pupil_ids.append(bebras_id)

      printYaml("models.Class", class_yaml_id,
        id=class_id, name=class_name, level=class_level, pupils=pupil_ids)
  elif type == "school":
    for i in range(0, number):
      school_id, school_name, (country, city, street, number), classes = generateSchool(randint(0, 20))
      school_yaml_id = "school" + str(school_id)
      
      class_names = []
      # Print klassen
      for c in classes:
        class_id, class_name, class_level, pupils = c
        class_yaml_id = "class" + str(class_id)
        pupil_ids = []
        
        for pupil in pupils:
          _, (fn, ln, email, bebras_id, password, gender, lang, birth) = pupil
          printYaml("models.Pupil", bebras_id,
            firstName = fn, lastName=ln, email=email,
            bebrasId = bebras_id, password=password, gender=gender,
            language=lang, birthday=birth)
          
          pupil_ids.append(bebras_id)
 
        printYaml("models.Class", class_yaml_id, id=class_id, name=class_name, level=class_level, pupils=pupil_ids)
        class_names.append(class_yaml_id)
      
      printYaml("models.School", school_yaml_id, id=school_id, name=school_name,
        country=country, city = city, street=street, number=number, classes=class_names)
  else:
    printUsage()

if __name__ == "__main__":
  if len(sys.argv) != 3:
    printUsage()
  else:
    main(sys.argv[1], int(sys.argv[2]))
