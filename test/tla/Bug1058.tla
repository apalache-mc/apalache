---- MODULE Bug1058 ----
EXTENDS Naturals

VARIABLE
  \* @type: Int -> Int;
  f

Init == 
  \/ f \in [{1} -> {}]
  \/ f \in [{} -> {}] 

Next == f' = f

====