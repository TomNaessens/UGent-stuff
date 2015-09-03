Tom Naessens
TomNaessens@UGent.be
1ste Bachelor Informatica
Universiteit Gent

##########################
#   GLOBAAL OVERZICHT    #
##########################

1. Packagestructuur
-------------------
Mijn project is voornamelijk opgedeeld volgens de structuur van het Model-View-Controller-principe. Deze zijn al dan niet nog eens opgedeeld volgens de 'soort' of volgens het programmadeel waarbij ze horen. 
In het package controllers is er een onderscheid gemaakt tussen controllers die achter knoppen zitten, muistekenaars,  controlelrs die bij diverse aspecten van de logger horen en controllers die bij het menu horen. Hiernaast zitten er nog enkele klassen 'los' in het package Controllers aangezien deze apart staan en toch te klein zijn om een extra onderverdeling voor aan te maken. 
Het Models-package is algemeen opgebouwd volgens de grote delen van het programma, namelijk de logger, de ontwerper en de simulator. Ook hier bevinden zich los nog enkele klassen die models voorstellen die algemeen gebruikt worden.
Als laatste package van de MVC-structuur is er het package Views. Ook dit package is opgebouwd volgens de algemene hoofddelen van het programma (Logger, Ontwerper, Simulator) en bevat nog enkele losse klassen die algemeen voorkomen. Bij het ontwerper-onderdeel in dit package is nog eens een subpackage gemaakt die alle panels bevat waar de parameters kunnen ingegeven worden.
Er zijn nog 2 extra packages, namelijk icons en utils. In icons bevinden zich alle icoontjes en een gemeenschappelijke bovenklasse die het merendeel van de code beheert. Utils bestaat uit diverse klassen die nergens echt thuis horen.
Uiteindelijk bevindt er zich 1 klasse los in het hoofdpackage, namelijk de klasse Elektrobank, waar de main methode van het hele programma zich in bevindt.

2. Componentenvoorstelling
--------------------------
Ik heb in dit project volledig de componenten van JOldeSpice gebruikt.

3. Gebruikte models
-------------------
(In alfabetische volgorde)
EdgeCircuitModel: Het EdgeCircuitModel is een bovenliggend waar zowel TekenModel als SimulatorModel van overerven. Dit model bevat het Edgecircuit zelf, alsook de dimensie van het teken- of simuleervenster. Het bevat ook enkele methodes om bijvoorbeeld het hele circuit te wissen of om een ander circuit in te stellen.
LoggerModel: Dit model houdt zowat alles bij wat nodig is om de logger te laten werken. Het houdt bij welk loggingniveau er geselecteerd is en welke logberichten we willen weergeven. Hiernaast houdt het ook een lijst bij van alle gelogde berichten zodat we deze later kunnen opvragen. Geregistreerde changelistener is ChangeList, die de lijst aanpast.
ParameterModel: Het ParameterModel houdt bij welk parameterpaneel er geselecteerd is. Dit paneel wordt aangepast door het SelectedComponetModel door op een knop te klikken waar een SelectedComponentController aan vast hangt of door het TekenModel als er een component geselecteerd wordt. Dit model houdt alle waardes bij van een bepaalde categorie en zorgt ervoor dat de juiste waarden getoond worden bij de juiste component. Hij zorgt er ook voor dat de juiste component wordt aangemaakt als het TekenModel een nieuw component nodig heeft. Geregistreerde luisteraars zijn alle textvelden die hun waardes veranderen op basis van wat er in dit model staat.
SelectedActionModel: Het SelectedActionModel houdt bij welke muishandler er moet geregistreerd worden bij het TekenPanel op basis van geselecteerde knoppen.
SelectedComponentModel: Het SelectedActionModel houdt bij welk icon er geselecteerd is op basis van geselecteerde knoppen.
SimulatorModel: Dit model beheert de hele simulatie. Zoals eerder vermeld gebruikt hij het circuit op basis van het circuit dat in EdgeCircuitModel staat. Dit model bevat een aantal methodes die de simulatie kunnen initialiseren, resetten, met 1 stap doen kunnn laten gaan. Het beheert ook de Timer die gebruikt wordt bij het 'loopen' van de simuatie en zorgt ervoor dat de interne staat van een switch kan worden aangepast. Het bevat verder nog alle info zodat de SimulatorMouseHandler de simulatie mooi kan tekenen.
TabbedModel: Het TabbedModel is een klein model dat ervoor zorgt dat bij het wisselen van tab in het SimulatorModel en het SelectedActionModel de juiste elementen geset worden.
TekenModel: Dit is globaal gezien het grootste model. Het bevat alle methodes die gebruikt worden bij het tekenen op het TekenPanel door de mousehandlers die hierbij geregistreerd zijn: DummyMouseHandler, NewComponentMouseHandler, MoveNodeMouseHandler en RemoveEdgeMouseHandler. 

Hiernaast bestaan er ook nog enkele 'gewone' models van Swing zelf:
SpinnerNumberModel: Deze wordt gebruikt door de spinners om de snelheid en de timestep van de simulator aan te passen.
DefaultListModel: Wordt gebruikt door de lijst van de logger.


4. Eigenaardigheden
-------------------
In mijn algemene structuur heb ik 1 overheersende klasse, genaamd: ModelBeheerder. Deze klasse bevindt zich in het package 'Models'. Deze klasse is geen 'model' op zichzelf, maar hij beheert wel alle modellen. (Daarom heb ik hem ook in dit package geplaatst.) Het is met andere woorden mogelijk om overal aan deze klasse alle andere modellen op te vragen. Dit heeft enkele voordelen:
- Het is mogelijk om in elke situatie informatie van een ander model op te halen of in een ander model te zetten;
- Het is veel overzichtelijker dan op verschillende plaatsen in de code modellen aan te maken;
- Het is efficienter bij het doorgeven van models van de ene contstructor naar de andere: als je bijvoorbeeld zowel in het menu listeners hebt die info in enkele bepaalde modellen veranderen, en ook andere listeners die zich ergens diep in het programma bevinden waar ongeveer 5 - 6 'lagen' views tussen zitten hoef je maar 1 model door te geven aan de contstructors van onderliggende views, en niet 2. Bij 2 modellen valt dit nog mee, maar als dat er 4 of 5 worden is het zo een stuk overzichtelijker.
Het enige nadeel van deze werking is dat als enkele modellen in elkaar worden aangemaakt je enkele hacks moet uithalen om nullpointers te voorkomen. Naar mijn mening verdwijnt deze ene ongemakkelijkheid in het niets tegen de voordelen die je er kan uit halen.


















