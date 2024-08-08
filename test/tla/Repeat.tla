------------------------ MODULE Repeat ------------------------------------
EXTENDS Apalache, Integers

Inv1 ==
    LET Op(a, i) == a + 1
    IN Repeat(Op, 5, 0) = 5

Inv2 ==
    LET Op(a, i) == a + i
    IN Repeat(Op, 5, 0) = 15

\* Cyclical Op: \E k: Op^k = Id
Inv3 ==
    LET Op(a,i) == (a + i) % 3
    IN LET
        v == 1
        x0 == Repeat(Op, 0, v)
        x3 == Repeat(Op, 3, v)
        x6 == Repeat(Op, 6, v)
    IN
        /\ v = x0
        /\ x0 = x3
        /\ x3 = x6

\* Idempotent Op: Op^2 = Op
Inv4 ==
    LET
        \* @type: (Set(Set(Int)), Int) => Set(Set(Int));
        Op(a, i) == {UNION a}
    IN LET
        v == {{1}, {2}, {3,4}}
        x1 == Repeat(Op, 1, v)
        x2 == Repeat(Op, 2, v)
        x3 == Repeat(Op, 3, v)
    IN
        /\ v /= x1
        /\ x1 = x2
        /\ x2 = x3

\* Nilpotent Op: \E k: Op^k = 0
Inv5 ==
    LET
        \* @type: (Set(Int), Int) => Set(Int);
        Op(a, i) == a \ { x \in a: \A y \in a: x <= y }
    IN LET
        v == {1,2,3}
        x1 == Repeat(Op, 2, v)
        x2 == Repeat(Op, 3, v)
        x3 == Repeat(Op, 4, v)
    IN
        /\ x1 /= x2
        /\ x2 = x3
        /\ x3 = {}


Init == TRUE
Next == TRUE

Inv ==
    /\ Inv1
    /\ Inv2
    /\ Inv3
    /\ Inv4
    /\ Inv5

===============================================================================
