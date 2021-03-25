----------------- MODULE Rec13 ----------------------                           
EXTENDS Integers

VARIABLE
    \* @type: Int;
    y

LOCAL Send[x \in { 1, 2}] ==
    x \* at this point, we expect x = 2, not x = 1

SendAll(x) == Send[x + 1]

Init == y = SendAll(1)

Next == UNCHANGED y

Inv == y = 2
=====================================================
