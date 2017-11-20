---------------------- MODULE assignmentTestQuantifiers ----------------------
VARIABLE a,b

Next == /\ \/ /\ a' = b'
              /\ b' = a'
           \/ \E p \in { 1, 2 } : b' = p
        /\ a' = 1
       
Init == /\ a = 0
        /\ b = 0
        
Spec == [][Next]_<< a,b >>     
==============================================================

