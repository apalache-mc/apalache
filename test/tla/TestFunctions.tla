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

AllTests ==
    /\ TestFunCtor
    /\ TestFunCtorSet
    /\ TestFunCtorSetToSet
    /\ TestFunCtorOnPowerset
    /\ TestFunSetToPowerset

================================================================================
