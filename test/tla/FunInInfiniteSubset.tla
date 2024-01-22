--------------- MODULE FunInInfiniteSubset -----------------

EXTENDS Integers

P == {"P1_OF_P"}

VARIABLE
    \* @type: P -> Set(Int);
    myVariable

Init ==
    myVariable = [p \in P |-> {0}]

Step(p) ==
    myVariable' = [q \in P |-> {0}]

Next == \E p \in P : Step(p)

TypeOkay == myVariable \in [P -> SUBSET Int]
TypeOkay_ == TypeOkay

=============================================
