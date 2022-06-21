---- MODULE LetIn ----

\* Tests behaviour when there are let-in expressions in the formula 

EXTENDS Integers

VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y

Init ==
    /\ x = 0
    /\ y = 1

Next ==
    /\ x' = y
    /\ y' = x

Liveness == 
    LET Plus(a,b) == a + b IN
    LET var1 == x IN
    []<>(Plus(Plus(var1,y), var1) = 2)
FalseLiveness == 
    LET Plus(a,b) == a + b IN
    LET var1 == x IN
    <>[](Plus(var1,y) = 2)

====