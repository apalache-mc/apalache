---------- MODULE Bug931 ----------
EXTENDS  FiniteSets

Init == TRUE
Next == TRUE
Inv == Cardinality({}) = 0

===================================
