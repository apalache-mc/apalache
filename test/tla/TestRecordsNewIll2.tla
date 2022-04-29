--------------------- MODULE TestRecordsNewIll2 -------------------------------
(*
 * Ill-typed access over new records.
 *)

(* TESTS *)
TestAccess ==
    \E r \in { [ a |-> 28, b |-> "abc" ] }:
        \* old records allow access non-existant fields
        r.c = 10

===============================================================================
