-------------------------------- MODULE Bug1136 -------------------------------
\* a regression test for a^b, see:
\* https://github.com/apalache-mc/apalache/issues/1136

EXTENDS Integers

VARIABLES
    \* @type: Int;
    base,
    \* @type: Int;
    power,
    \* @type: Int;
    exp

Init ==
    /\ base = 3
    /\ power = 1
    /\ exp = 3

Next ==
    /\ power' = power + 1
    /\ exp' = exp * base
    /\ UNCHANGED base

Inv ==
    exp = base^power
    
===============================================================================
