---- MODULE ConstantOperator ----

CONSTANTS
    \* @type: Set(Int);
    A,
    \* @type: Set(Int);
    B,
    \* Whether two numbers are good together.
    \* @type: (Int, Int) => Bool;
    AreGood(_, _)

GOOD_PAIR_EXISTS == \E a \in A, b \in B: AreGood(a, b)

====