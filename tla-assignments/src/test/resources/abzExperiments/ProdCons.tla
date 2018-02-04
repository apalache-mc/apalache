------------------------------ MODULE ProdCons ------------------------------

VARIABLE S, empty

Init == S = {} /\ empty = TRUE

Produce == /\ empty' = FALSE
           /\ \E X \in SUBSET {"A", "B", "Z", "1", "8"} : S' = S \cup { X }

Consume == ~ empty /\ S' \in SUBSET S /\ empty' = (S' = {})

Next == Produce \/ Consume

=============================================================================
