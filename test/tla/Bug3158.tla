-------------------------------- MODULE Bug3158 -------------------------------
\* Function generators were producing counterexamples with junk,
\* even though the internal representation in SMT seems to be sound.
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
