-------------------------------- MODULE Bug3158 -------------------------------
\* the buggy generators were not able to produce functions of empty domain
EXTENDS Integers, FiniteSets, Apalache

VARIABLE
  \* @type: Int -> Int;
  fun

Init ==
  fun = Gen(4)

Next ==
  UNCHANGED fun

Inv ==
  DOMAIN fun /= {}
===============================================================================
