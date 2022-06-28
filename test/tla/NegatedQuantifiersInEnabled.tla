---- MODULE NegatedQuantifiersInEnabled ----

\* Tests behaviour when there are 
\* superfluous box operators in the formula

EXTENDS Integers

VARIABLES
    \* @type: Int;
    x

Init ==
    /\ x = 0

XIsNotSmall ==
    /\ ~\E i \in {0,1}: x = i
    /\ x' = 1

Next ==
    XIsNotSmall \/ UNCHANGED x

FalseLiveness == <>(<<ENABLED XIsNotSmall>>_x)



====