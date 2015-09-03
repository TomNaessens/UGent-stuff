---- MODULE Treinprotocol ----
VARIABLES aanBoord, deurenGesloten, signaal, seinlicht, treinVertrokken, laatsteOpen
----

vars == <<aanBoord,deurenGesloten,signaal,seinlicht,treinVertrokken,laatsteOpen>>

Signalen == {"geen","AC"}
Seinen == {"geen","rood","wit"}

TypeOK == /\ aanBoord \in BOOLEAN
          /\ deurenGesloten \in BOOLEAN
          /\ signaal \in Signalen
          /\ seinlicht \in Seinen
          /\ treinVertrokken \in BOOLEAN
          /\ laatsteOpen \in BOOLEAN

Init == /\ aanBoord = TRUE
        /\ deurenGesloten = FALSE
        /\ signaal = "geen"
        /\ seinlicht = "geen"
        /\ treinVertrokken = FALSE
        /\ laatsteOpen = TRUE

(* mogelijke acties *)
SluitDeuren == /\ aanBoord
               /\ ~deurenGesloten
               /\ deurenGesloten' = TRUE
               /\ aanBoord' = FALSE
               /\ UNCHANGED <<signaal,seinlicht,treinVertrokken,laatsteOpen>>

GeefStartSign == /\ ~aanBoord
                 /\ deurenGesloten = TRUE
                 /\ ~treinVertrokken
                 /\ signaal' = "AC"
                 /\ seinlicht' = "rood"
                 /\ UNCHANGED <<aanBoord,deurenGesloten,treinVertrokken,laatsteOpen>>

StapOp == /\ ~aanBoord
          /\ signaal = "AC"
          /\ ~treinVertrokken
          /\ aanBoord' = TRUE
          /\ UNCHANGED <<deurenGesloten,signaal,seinlicht,treinVertrokken,laatsteOpen>>

VertrekSignaal == /\ seinlicht = "rood"
                  /\ seinlicht' = "wit"
                  /\ UNCHANGED <<aanBoord,deurenGesloten,signaal,treinVertrokken,laatsteOpen>>

TreinVertrek == /\ seinlicht = "wit"
                /\ treinVertrokken' = TRUE
                /\ UNCHANGED <<aanBoord,deurenGesloten,signaal,seinlicht,laatsteOpen>>

SluitLaatste == /\ treinVertrokken
                /\ aanBoord
                /\ laatsteOpen
                /\ laatsteOpen' = FALSE
                /\ UNCHANGED <<aanBoord,deurenGesloten,signaal,seinlicht,treinVertrokken>>

Next == SluitDeuren \/ GeefStartSign \/ StapOp \/ VertrekSignaal \/ TreinVertrek \/ SluitLaatste

Live == /\ WF_vars(SluitDeuren)
        /\ WF_vars(GeefStartSign)
        /\ WF_vars(StapOp)
        /\ WF_vars(VertrekSignaal)
        /\ WF_vars(TreinVertrek)
        /\ WF_vars(SluitLaatste)

Protocol == Init /\ [][Next]_vars /\ Live
----
TreinVertrekt == Init ~> treinVertrokken
TreinMetGeslotenDeuren == treinVertrokken => deurenGesloten
LaatsteDeurGesloten == treinVertrokken ~> (~laatsteOpen /\ deurenGesloten)
BegeleiderAanBoord == treinVertrokken => aanBoord
----
THEOREM Protocol => []TypeOK
THEOREM Protocol => TreinVertrekt
THEOREM Protocol => []TreinMetGeslotenDeuren
THEOREM Protocol => LaatsteDeurGesloten
THEOREM Protocol => []BegeleiderAanBoord
====
