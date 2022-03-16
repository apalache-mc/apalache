-------------------------- MODULE TestFunctions --------------------------------
EXTENDS Integers

Init == TRUE
Next == TRUE

TestFunCtor ==
    LET fun == [ x \in 1..10000 |-> x + 1 ] IN
    fun[5000] = 5001

AllTests ==
    /\ TestFunCtor

================================================================================
