------------------------------ MODULE FormulaRefs -----------------------------
\* A test for the subformula syntax e.g., A!2.
\* Apalache should show a parse error.
EXTENDS Integers

VARIABLES
    \* @type: Int;
    x

A ==
    /\ x > 3
    /\ x > 2

B(y) ==
    /\ y > 3
    /\ y > 2

Init ==
    x = 2

Next ==
    x' = x

Inv1 ==
    A!1

Inv2 ==
    A!2

Inv4 ==
    B(x)!1

Inv5 ==
    B(x)!2

===============================================================================
