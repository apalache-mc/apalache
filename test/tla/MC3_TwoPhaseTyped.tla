---------------------------- MODULE MC3_TwoPhaseTyped -------------------------

RM == { "0_OF_RM", "1_OF_RM", "2_OF_RM" }

VARIABLES
  \* @type: RM -> Str;
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  \* @type: Str;
  tmState,       \* The state of the transaction manager.
  \* @type: Set(RM);
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
  \* @type: Set($message);
  msgs

INSTANCE TwoPhaseTyped
===============================================================================
