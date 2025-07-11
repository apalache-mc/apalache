------------------------ MODULE MC50_TwoPhaseTypedInv -------------------------

RM == {
    "0_OF_RM", "1_OF_RM", "2_OF_RM", "3_OF_RM", "4_OF_RM", "5_OF_RM",
    "6_OF_RM", "7_OF_RM", "8_OF_RM", "9_OF_RM", "10_OF_RM", "11_OF_RM",
    "12_OF_RM", "13_OF_RM", "14_OF_RM", "15_OF_RM", "16_OF_RM", "17_OF_RM",
    "18_OF_RM", "19_OF_RM", "20_OF_RM", "21_OF_RM", "22_OF_RM", "23_OF_RM",
    "24_OF_RM", "25_OF_RM", "26_OF_RM", "27_OF_RM", "28_OF_RM", "29_OF_RM",
    "30_OF_RM", "31_OF_RM", "32_OF_RM", "33_OF_RM", "34_OF_RM", "35_OF_RM",
    "36_OF_RM", "37_OF_RM", "38_OF_RM", "39_OF_RM", "40_OF_RM", "41_OF_RM",
    "42_OF_RM", "43_OF_RM", "44_OF_RM", "45_OF_RM", "46_OF_RM", "47_OF_RM",
    "48_OF_RM", "49_OF_RM"
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
