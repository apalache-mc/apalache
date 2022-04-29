--------------------- MODULE TestRecordsNewIll4 -------------------------------
EXTENDS Integers

(*
 * Ill-typed access over new records.
 *)

(* TESTS *)
TestAccess ==
    LET r1 == [ a |-> 28, b |-> "abc" ] IN
    \* old records allow access non-existant fields
    r1 \in [ a: 1..3, b: { "foo", "bar" }, c: BOOLEAN ]
===============================================================================
