--------------------- MODULE TestRecordsNewIll1 -------------------------------
(*
 * Ill-typed access over new records.
 *)

(* TESTS *)
TestCtor ==
    \* the new records do not allow to shrink/expand the domain
    { [ a |-> 28, b |-> "abc" ], [ a |-> 10 ] } /= {}
===============================================================================
