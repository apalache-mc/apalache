----------------------------- MODULE Callback ----------------------------
EXTENDS Integers

VARIABLES x

Pick(Cb(_)) ==
    \E i \in 1..10:
        Cb(i)

Init ==
    LET Cb(i) ==
        x = i
    IN
    Pick(Cb)

Next ==
    LET Cb(i) ==
        x' = i
    IN
    Pick(Cb)

Inv ==
    x > 0
==========================================================================
