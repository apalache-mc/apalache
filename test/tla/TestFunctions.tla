-------------------------- MODULE TestFunctions --------------------------------
EXTENDS Integers, FiniteSets

Init == TRUE
Next == TRUE

TestFunCtor ==
    LET fun == [ x \in 1..10000 |-> x + 1 ] IN
    \E i \in DOMAIN fun:
        fun[i] = i + 1

TestFunCtorSet ==
    LET fun == [ x \in 1..100 |-> { x } ] IN
    fun[50] = { 50 }

TestFunCtorSetToSet ==
    LET Singletons == { { x }: x \in 1..100 } IN
    LET fun == [ x \in Singletons |-> { x } ] IN
    fun[{ 50 }] = { { 50 } }

TestFunCtorOnPowerset ==
    [ S \in SUBSET BOOLEAN |-> Cardinality(S) ] =
        [ S \in { {}, {FALSE}, {TRUE}, {FALSE, TRUE} } |->
            Cardinality(S) ]

TestFunSetToPowerset ==
    \A f \in [ BOOLEAN -> SUBSET BOOLEAN ]:
        /\ DOMAIN f = BOOLEAN
        /\ \A x \in BOOLEAN:
            f[x] \in SUBSET BOOLEAN

TestFunFromFunSet ==
    \* Introduce cells via LET-IN, so they do not get optimized.
    LET x == 1 IN
    LET y == 2 IN
    LET S == { 0, x, y - 1 } IN
    LET T == 3..6 IN
    \* This will get negated when checking the invariant.
    \* Note that x = y - 1, but the model checker does not statically deduce it.
    \* Hence, a sound implementation must ensure that the equal elements of S
    \* are mapped on the same elements of T.
    \A f \in [ S -> T ]:
        /\ f[x] = f[y - 1]
        /\ S = DOMAIN f
        /\ \A e \in S:
            f[e] \in T

AllTests ==
    /\ TestFunCtor
    /\ TestFunCtorSet
    /\ TestFunCtorSetToSet
    /\ TestFunCtorOnPowerset
    /\ TestFunSetToPowerset
    /\ TestFunFromFunSet

================================================================================
