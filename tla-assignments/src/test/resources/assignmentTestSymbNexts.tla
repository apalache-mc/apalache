---------------------- MODULE assignmentTestSymbNexts ----------------------
CONSTANT A, X, Y, T1, T2
VARIABLE a,b

Next == /\ a' \in A
        /\ \/ /\ b' \in X
              /\ T1
           \/ /\ b' \in Y
              /\ T2

NexT == /\ a' \in A
        /\ b' = 1
        /\ \/ a' = 1
           \/ a' = 2
           \/ /\ 0 = 1
              /\ a' = 3

Init == /\ a = 0
        /\ b = 0

Spec == [][Next]_<< a,b >>
==============================================================

