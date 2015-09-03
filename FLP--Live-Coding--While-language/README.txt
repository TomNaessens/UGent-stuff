-- -- --| Project: Functionele en Logische Programmeertalen
-- -- --| Deel: Haskell
-- -- --| Auteur: Tom Naessens
-- -- --| File: README.txt

-- --| Opmerkingen
* BELANGRIJK: De resulterende HTML rekent erop dat de folder libs/ zich in de zelfde map
  bevindt als de HTML aangezien de jQuery bibliotheek en de stijlbestanden
  zich daar in bevinden

* Ontwikkeld en gecompileerd met : The Glorious Glasgow Haskell
                                   Compilation System, version 6.12.3

-- --| Extra's!
* Cabal                          : Dit project kan met cabal gecompileerd worden
                                   met commando's:
                                   cabal configure
                                   cabal build
                                   cabal install

* Lusontvouwing : Zoals je kan zien in example.html geeft dit programma niet
                  enkel de originele code terug, maar breidt het de uitvoer
                  uit met de while-lusontvouwing om zo gemakkelijker als
                  programmeur te kunnen kijken welke lussen precies waar en
                  wanneer worden uitgevoerd.
                  Mijn oorspronkelijk idee was om het originele programma met
                  'dichtgevouwen' lussen zoals in het voorbeeld ook terug te
                  geven maar dit is me niet meer gelukt voor de deadline.

* HTML & JQuery : Als output heb ik gekozen voor een combinatie van HTML met
                  JQuery. De while loops zijn collapsable als je er op klikt.

-- --| Bestanden met hun functies
--| Core files
* Main.hs          : De main file van dit project: neemt een file als argument,
                     en print de 'livecoded' versie van deze file uit,
                     gebruikt alle andere files.
* DataTypes.hs     : De definitie van de belangrijkste datatypes. Gebruikt
                     doorheen het project.
* ParserM.hs       : Deels de parserM die werd meegegeven bij Set5, aangevuld
                     met eigen functies uit Set4, Set5 en nieuwe functies.
* WhileParser.hs   : Neemt een String als input en parset deze volledig tot
                     een AST.
* LiveCoding.hs    : Neemt een AST als input en geeft een lijst van tuples van
                     het type (Statement, VarMap) terug.
* PrettyPrinter.hs : Neemt de lijst uit LiveCoding en pretty print het.

--|Example input files
* example/
  * prog1.txt : Standaard input: 1 eenvoudige whilelus
  * prog2.txt : Randgeval: 1 enkele assignment, niets anders
  * prog3.txt : Iets complexer: geneste while
  * prog4.txt : Complexere while met complexere berekeningen
                (cfr. While programma van Thomas Soens)

--|Tests
* tests/
  WhileOntvouwing : Een uitwerking om de whileontvouwing te testen,
                    zonder bewijs echter

--|Libraries
* libs/
  jquery.min.js : De JQuery bibliotheek, nodig voor de html output

--|Voorbeeldoutput
* voorbeeld.html : Een voorbeelduitvoer van het programma, opgesteld aan
                   de hand van example/prog3.txt
