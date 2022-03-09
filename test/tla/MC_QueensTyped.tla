---------------------------- MODULE MC_QueensTyped ----------------------------
\* an instance of QueensTyped for model checking.
N == 4

VARIABLES
    \* @type: Set(Seq(Int));
    todo,
    \* @type: Set(Seq(Int));
    sols

INSTANCE QueensTyped
===============================================================================
