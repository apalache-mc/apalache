---- MODULE ConstantOperatorImpl ----

CONSTANTS
    \* @type: Set(Int);
    A,
    \* @type: Set(Int);
    B

\* @type: (Int, Int) => Bool;
Equal(x, y) == x = y

INSTANCE ConstantOperator WITH AreGood <- Equal

====