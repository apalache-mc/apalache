------------------------------- MODULE ActionInv ------------------------------
\* testing action invariants
EXTENDS Integers

VARIABLE
    \* @type: Int;
    x

Init ==
    x = 0

Next ==
    x' = x + 1 \/ x' = x + 2

\* this is a state invariant, as it refers to x, but not x'
NonNegativeInv ==
    x >= 0
    
\* a false state invariant
PositiveInv ==
    x > 0

\* this is an action invariant, as it refers to x'
IncreaseInv ==
    x' > x

\* a false action invariant
KeepInv ==
    x' = x

===============================================================================
