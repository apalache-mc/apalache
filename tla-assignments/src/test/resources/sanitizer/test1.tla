---------------------- MODULE test1 ----------------------
CONSTANT e,f,g
VARIABLE a,b,c,d,x,y,z

Next == /\ a' = 1
        /\ b' = (e = f)
        /\ c' \in { e,f,g }
        /\ d' = 4
        /\ UNCHANGED <<x,y>>
        /\ UNCHANGED z
       
Init == a = 0
        
Spec == [][Next]_<< a,b >>     
==============================================================

