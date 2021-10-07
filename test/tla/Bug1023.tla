----------------------- MODULE Bug1023 ----------------------------------------
\* An MWE that demonstrates that ConstInit does not propagate constraints.
\* It reports an error when run with:
\*   apalache check --cinit=ConstInit --inv=Inv Bug1023.tla
EXTENDS Integers

CONSTANTS
  \* @type: Int;
  t_min,
  \* @type: Int;
  t_max

ConstInit ==
  /\ t_min \in Int
  /\ t_max \in Int
  /\ t_min <= t_max

Init ==
  TRUE

Next ==
  TRUE

Inv ==
  t_min <= t_max

===============================================================================
