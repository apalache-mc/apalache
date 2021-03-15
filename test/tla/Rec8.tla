------------------------------ MODULE Rec8 ------------------------------------
EXTENDS Integers

VARIABLES
    \* @type: Int;
    n,
    \* @type: Int;
    factSpec,
    \* @type: Int;
    factComp

\* the syntax for type annotations
a <: b == a

\* the type of the factorial function
FactT == [Int -> Int]

(*
 Defining a recursive function on a finite domain. Although it is rather
 unnatural to define factorial on a finite set, both Apalache and TLC
 require finite domains. As is usual for function application, the result
 of the application is not defined on the elements outside of the function
 domain.
 *)
Fact[k \in 1..20] ==
    IF k <= 1
    THEN 1
    ELSE k * (Fact <: FactT)[k - 1]

Init ==
    /\ n = 1
    /\ factSpec = Fact[n]
    /\ factComp = 1

Next ==     
    /\ n' = n + 1
    /\ factSpec' = Fact[n']
    /\ factComp' = n' * factComp

Inv ==
    factComp = factSpec

===============================================================================
