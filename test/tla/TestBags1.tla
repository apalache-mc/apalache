------------------------------ MODULE TestBags1 -----------------------
EXTENDS Integers, Bags

VARIABLES bag

\* the base of our multiset
Base == 0..3

Init ==
    bag = EmptyBag

Next ==
    \/ \E x \in Base: bag' = bag + SetToBag({x})
    \/ \E x \in Base: bag' = bag - SetToBag({x})

=======================================================================
