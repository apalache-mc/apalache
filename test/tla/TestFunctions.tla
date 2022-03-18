-------------------------- MODULE TestFunctions --------------------------------
EXTENDS Integers

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

AllTests ==
    /\ TestFunCtor
    /\ TestFunCtorSet
    /\ TestFunCtorSetToSet

================================================================================
