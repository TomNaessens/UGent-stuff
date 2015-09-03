---------------------- MODULE HourClock3ter ---------------------
EXTENDS HourClock

HCini3  ==  hr \in (0 .. 11)
HCnxt3  ==  hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC3  ==  HCini3 /\ [][HCnxt3]_hr
--------------------------------------------------------------
THEOREM  HC3 => []HCini3
==============================================================
