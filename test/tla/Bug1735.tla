---- MODULE Bug1735 ----

EXTENDS Integers

Init == TRUE
Next == TRUE

Inv ==
    LET f == [ x \in {2} |-> 2 ] IN
    LET S == [{ 1, 2 } -> { 2 }] IN
    f \in S

=================