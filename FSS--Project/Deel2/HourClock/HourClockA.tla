---------------------- MODULE HourClockA ---------------------
EXTENDS Naturals
VARIABLE hr
HCini  ==  hr \in (1 .. 12)
HCnxt  ==  hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC  ==  HCini /\ [][HCnxt]_hr /\ WF_hr(HCnxt)
--------------------------------------------------------------
THEOREM  HC => []HCini
==============================================================
