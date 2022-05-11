------------------------- MODULE TestRecordsNew -------------------------------
(*
 * Functional tests for operators over new records.
 * We introduce a trivial state machine and write tests as state invariants.
 *)

EXTENDS Integers

Init == TRUE
Next == TRUE

(* DEFINITIONS *)

(* TESTS *)
TestCtor ==
    { [ a |-> 28, b |-> "abc" ], [ a |-> 10, b |-> "def" ] } /= {}

TestRecCtor ==
    [ a: { 10 }, b: { "abc", "def" } ] =
        { [ a |-> 10, b |-> "abc" ], [ a |-> 10, b |-> "def" ] }

TestRowAccess ==
    \* GetA is polymorphic in r
    LET \* @type: { a: b, c } => b;
        GetA(r) == r.a
    IN
    LET r1 == [ a |-> 10, b |-> "abc" ] IN
    LET r2 == [ a |-> 10, c |-> TRUE ] IN
    \* although r1 and r2 have different types, GetA returns Int
    GetA(r1) = GetA(r2)

TestRowUpdate ==
    \* SetA is polymorphic in r
    LET \* @type: ({ a: b, c }, b) => { a: b, c };
        SetA(r, i) == [ r EXCEPT !.a = i ]
    IN
    LET r1 == SetA([ a |-> 10, b |-> "abc" ], 2) IN
    LET r2 == SetA([ a |-> 10, c |-> TRUE ], 2) IN
    \* although r1 and r2 have different types, their fields "a" are equal
    r1.a = r2.a

TestDomain ==
    LET r1 == [ a |-> 10, b |-> "abc" ] IN
    LET r2 == [ a |-> 20, b |-> TRUE ] IN
    \* although r1 and r2 have different types, their domains are equal
    DOMAIN r1 = DOMAIN r2

TestRecExists ==
    \E r \in [ a: { 10, 20 }, b: { "abc", "def" } ]:
        /\ r.a \in { 10, 20}
        /\ r.b \in { "abc", "def" }

AllTests ==
    /\ TestCtor
    /\ TestRecCtor
    /\ TestRowAccess
    /\ TestRowUpdate
    /\ TestDomain
    /\ TestRecExists

===============================================================================
