-------------------------- MODULE BakeryTyped --------------------------------

CONSTANT
    \* @type: Int;
    N

VARIABLES
    \* @type: Int -> Int;
    num,
    \* @type: Int -> Bool;
    flag,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Set(Int);
    unchecked,
    \* @type: Int -> Int;
    max,
    \* @type: Int -> Int;
    nxt

ConstInit4 ==
    N = 4

INSTANCE BakeryWoTlaps
==============================================================================

