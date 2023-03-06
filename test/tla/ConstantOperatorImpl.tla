---- MODULE ConstantOperatorImpl ----

CONSTANTS
    \* @type: Set(Int);
    A,
    \* @type: Set(Int);
    B

\* @type: (Int, Int) => Bool;
Equal(x, y) == x = y

\* @type: (Int, Int) => Bool;
NotEqual(x, y) == x /= y

EqualsAreGoodAndEqualElements == INSTANCE ConstantOperator WITH
    A <- { 0, 1 },
    B <- { 1, 2 },
    AreGood <- Equal

EqualsAreGoodButNoEqualElements == INSTANCE ConstantOperator WITH
    A <- { 0, 1 },
    B <- { 2, 3 },
    AreGood <- Equal

InequalsAreGoodAndInequalElements == INSTANCE ConstantOperator WITH
    A <- { 0, 1 },
    B <- { 2, 3 },
    AreGood <- NotEqual

InequalsAreGoodButOnlyEqualElements == INSTANCE ConstantOperator WITH
    A <- { 2 },
    B <- { 2 },
    AreGood <- NotEqual

Init == TRUE
Next == TRUE
Inv == /\ EqualsAreGoodAndEqualElements!GOOD_PAIR_EXISTS
       /\ InequalsAreGoodAndInequalElements!GOOD_PAIR_EXISTS
       /\ ~EqualsAreGoodButNoEqualElements!GOOD_PAIR_EXISTS
       /\ ~InequalsAreGoodButOnlyEqualElements!GOOD_PAIR_EXISTS

====
