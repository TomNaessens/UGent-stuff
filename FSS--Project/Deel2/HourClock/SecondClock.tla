---------------------- MODULE SecondClock ----------------------
EXTENDS Naturals
VARIABLES hr, min, sec
SCini  ==  hr \in (0 .. 23) /\ min \in (0 .. 59) /\ sec \in (0 .. 59)
SCnxt  ==  /\ sec' = IF sec # 59 THEN sec+1 ELSE 0
       	   /\ min' = IF sec # 59 THEN min ELSE IF min # 59 THEN min + 1 ELSE 0
       	   /\ hr' = IF (sec # 59 \/ min # 59) THEN hr ELSE IF hr # 23 THEN hr + 1 ELSE 0
SC  ==  SCini /\ [][SCnxt]_<<hr,min>>
--------------------------------------------------------------
THEOREM  SC => []SCini
==============================================================
