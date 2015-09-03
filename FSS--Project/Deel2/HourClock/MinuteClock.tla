---------------------- MODULE MinuteClock ----------------------
EXTENDS Naturals
VARIABLES hr, min
MCini  ==  hr \in (0 .. 23) /\ min \in (0 .. 59)
MCnxt  ==  /\ min' = IF min # 59 THEN min+1 ELSE 0
       	   /\ hr' = IF min # 59 THEN hr ELSE IF hr # 23 THEN hr + 1 ELSE 0
MC  ==  MCini /\ [][MCnxt]_<<hr,min>>
--------------------------------------------------------------
THEOREM  MC => []MCini
==============================================================
