---- MODULE Kruispunt ----
VARIABLES lh, lz, beurt, detect
----
(* uitdrukking voor tuple met alle veranderlijken *)
vars = <<lh, lz, beurt, detect>>
Kleuren == {"groen","rood"}
Beurten == {"H","Z"}

Types == /\ lh \in Kleuren
         /\ lz \in Kleuren
         /\ beurt \in Beurten
         /\ detect \in {0,1}

(* begintoestand *)
Init == /\ detect = 0
        /\ lh = "groen"
        /\ lz = "rood"
        /\ beurt = "Z"

(* acties *)
Detectie == detect' = 1 /\ UNCHANGED <<lh,lz,beurt>>

HRood == /\ lh' = "rood"
         /\ lh = "groen"
         /\ lz = "rood"
         /\ beurt = "Z"
         /\ detect = 1
         /\ UNCHANGED <<lz,beurt,detect>>

ZGroen == /\ lz' = "groen"
          /\ beurt' = "H"
          /\ lz = "rood"
          /\ lh = "rood"
          /\ beurt = "Z"
          /\ UNCHANGED <<lh,beurt,detect>>

ZRood == /\ lz' = "rood"
         /\ lz = "groen"
         /\ beurt = "H"
         /\ UNCHANGED <<lh,beurt,detect>>

HGroen == /\ lh' = "groen"
          /\ beurt' = "Z"
          /\ lh = "rood"
          /\ lz = "rood"
          /\ beurt = "H"
          /\ UNCHANGED <<lz,beurt,detect>>

(* samenvatting acties *)
Next == \/ Detectie
        \/ HRood
        \/ ZGroen
        \/ ZRood
        \/ HGroen

(* Fairness-voorwaarden *)
Live == /\ WF_vars(HRood)
        /\ WF_vars(ZGroen)
        /\ WF_vars(ZRood)
        /\ WF_vars(HGroen)

(* specificatie *)
Spec == Init /\ [][Next]_vars /\ Live
----
UniekGroen == \/ lz # "groen"
              \/ lh # "groen"
ZijDetectieGroen == (detect = 1 /\ lz = "rood") ~> (lz = "groen")
GroenDefault == []<>(lh = "groen")
DetectieNodig == ENABLED<<ZGroen>>_vars => detect = 1
NietPermanentRood == []<>(~(lh = "rood" /\ lz = "rood"))
----
(* de te testen eigenschappen *)
THEOREM Spec => []Types
THEOREM Spec => []UniekGroen
THEOREM Spec => ZijDetectieGroen
THEOREM Spec => GroenDefault
THEOREM Spec => []DetectieNodig
THEOREM Spec => NietPermanentRood
====
