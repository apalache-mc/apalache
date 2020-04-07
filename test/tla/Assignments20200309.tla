----- MODULE Assignments20200309 -----
VARIABLE a
\* this specification fails, as there it has no expression
\* that can be treated as an assignment
Init == TRUE
Next == a' = a
Inv == FALSE
===============
