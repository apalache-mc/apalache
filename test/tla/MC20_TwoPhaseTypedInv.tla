------------------------ MODULE MC20_TwoPhaseTypedInv -------------------------

RM == {
    "0_OF_RM", "1_OF_RM", "2_OF_RM", "3_OF_RM", "4_OF_RM", "5_OF_RM",
    "6_OF_RM", "7_OF_RM", "8_OF_RM", "9_OF_RM", "10_OF_RM", "11_OF_RM",
    "12_OF_RM", "13_OF_RM", "14_OF_RM", "15_OF_RM", "16_OF_RM", "17_OF_RM",
    "18_OF_RM", "19_OF_RM"
}

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

INSTANCE TwoPhaseTypedInv
===============================================================================
