------------------------------ MODULE reorderTest ------------------------------

EXTENDS Integers 

VARIABLE v1, v2

Init == v1 = 1 /\ v2 = 1

S == {1}

\* As the use-case constraint produced by (3) is not an assignment SMT constraint,
\* the SMT-based assignment solver has 3 solutions:
\*  - pick (2) and (4) as assignments, forced (2) < (4)
\*  - pick (2) and (1) as assignments, arbitrary (2) < (1)
\*  - pick (2) and (1) as assignments, arbitrary (1) < (2)

\* MayFail can only be reordered in the last case, i.e., if
\* a) the SMT solver arbitrarily picks (1) as the v1 assignment and
\* b) the SMT solver arbitrarily picks the assignment order (1) < (2)

\* In left-to-right processing, (1) is always chosen and the formula order
\* is already correct
MayFail == /\ v1' = 1     \* (1)
           /\ \E x \in S: 
             /\ v2' = x   \* (2)
             /\ v1' > 0   \* (3)
           /\ v1' = v2'   \* (4)
           

\* MustFail cannot be reordered, because (2) has a use-case dependency
\* on (4) (and (3) on (1)), but the \E blocks are reordered as a single unit

\* In left-to-right processing, assignments do not exist, due to the 
\* assignment-before-use paradigm
MustFail == /\ \E x \in S: 
              /\ v1' = x   \* (1)
              /\ v2' > 0   \* (2)
            /\ \E y \in S: 
              /\ v2' = y   \* (3)
              /\ v1' > 0   \* (4)

=============================================================================


