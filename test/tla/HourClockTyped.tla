------------------- MODULE HourClockTyped --------------------
\* This is a local copy of the example from Specifying Systems:
\* https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/RealTime/HourClock.tla
EXTENDS Naturals

VARIABLE
  \* @type: Int;
  hr
HCini  ==  hr \in (1 .. 12)
HCnxt  ==  hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC  ==  HCini /\ [][HCnxt]_hr

TypeOK == hr \in (1 .. 12)
--------------------------------------------------------------
THEOREM  HC => []HCini
==============================================================
