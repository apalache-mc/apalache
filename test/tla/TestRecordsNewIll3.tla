--------------------- MODULE TestRecordsNewIll3 -------------------------------
(*
 * Ill-typed access over new records.
 *)

(* TESTS *)
TestAccess ==
    LET r1 == [ a |-> 28, b |-> "abc" ] IN
    \* old records allow access non-existant fields
    LET r2 == [ r1 EXCEPT !.c = TRUE ] IN
    DOMAIN r2 = { "a", "b" }
===============================================================================
