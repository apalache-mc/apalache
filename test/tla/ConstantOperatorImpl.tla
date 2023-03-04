---- MODULE ConstantOperatorImpl ----

CONSTANTS
    \* @type: Set(Int);
    A,
    \* @type: Set(Int);
    B

\* @type: (Int, Int) => Bool;
Equal(x, y) == x = y

Success == INSTANCE ConstantOperator WITH
    A <- { 0, 1 },
    B <- { 1, 2 },
    AreGood <- Equal

Failure == INSTANCE ConstantOperator WITH
    A <- { 0, 1 },
    B <- { 2, 3 },
    AreGood <- Equal

ASSUME Success!GOOD_PAIR_EXISTS
ASSUME ~Failure!GOOD_PAIR_EXISTS

Init == TRUE
Next == TRUE

====