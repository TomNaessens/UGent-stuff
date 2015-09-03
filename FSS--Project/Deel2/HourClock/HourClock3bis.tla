---------------------- MODULE HourClock3bis ---------------------
EXTENDS HourClock

HCini3  ==  hr \in (0 .. 11)
HCnxt3  ==  hr' = IF hr # 11 THEN hr + 1 ELSE 0
HC3  ==  HCini3 /\ [][HCnxt3]_hr
--------------------------------------------------------------
THEOREM HC <=> HC3
==============================================================
