-------------------- MODULE Test928 ---------------------------

Init == TRUE
Next == TRUE
Inv1 == \A x \in {}: x = 1
Inv2 == \A x \in {}: TRUE
Inv3 == \A x \in {}: FALSE
Inv4 == \E x \in {}: x = 1
Inv5 == \A x \in {}: TRUE
Inv6 == \A x \in {}: FALSE

NoFail == 
  \/ Inv1
  \/ Inv2
  \/ Inv3
  \/ Inv4
  \/ Inv5
  \/ Inv6

Fail == (CHOOSE x \in {}: TRUE) = (CHOOSE x \in {}: TRUE)

=============================================================================    
