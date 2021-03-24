----- MODULE Bug20190921 -----
EXTENDS Integers

\* constants and variables should propagate
\* in the transformations
CONSTANT
    \* @type: Int;
    N

VARIABLE
    \* @type: Int;
    x

CInit == N \in 1..10

Init == x = 0

Next == x < N /\ x' = x + 1

==============================
