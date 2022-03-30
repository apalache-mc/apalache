--------------------- MODULE MC_FoldExcept7 ---------------------------------

Proc == { "p1", "p2", "p3", "p4", "p5", "p6", "p7" }

VARIABLES
    \* Process clocks
    \*
    \* @type: Str -> Int;
    clocks,
    \* Drift between pairs of clocks
    \*
    \* @type: <<Str, Str>> -> Int;
    drift

INSTANCE FoldExcept    

==============================================================================
