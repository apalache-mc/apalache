--------------- MODULE test3 -------------
EXTENDS Integers
VARIABLE msgs, maxBal,maxVBal,maxVal

Quorum == {{1, 2}, {2, 3}, {1, 3}}

Send(m) == msgs' = msgs \cup {m}

Phase2a(b, v) ==
  /\ (~(\E m \in msgs : m.type = "2a" /\ m.bal = b ))
  /\ \E Q \in Quorum :
    LET Q1b == {m \in msgs : /\ m.type = "1b"
                             /\ m.acc \in Q
                             /\ m.bal = b}
        Q1bv == {m \in Q1b : m.mbal \geq 0}
    IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a 
        /\ \/ Q1bv = {}
           \/ \E m \in Q1bv : 
                /\ m.mval = v
                /\ \A mm \in Q1bv : m.mbal \geq mm.mbal 
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>
============================================