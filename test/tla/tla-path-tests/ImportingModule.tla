---- MODULE ImportingModule ----------------------------------------------------
(* This MODULE just checks whether it can import ImportedModule.

   It is meant to be run from outside of the tla-path-tests directory, with

     TLA_PATH=./tla-path-tests apalache-mc check ./tla-path-tests/ImportingModule.tla

   If checking succeeds, THEN TLA_PATH has worked as expected.
*)

EXTENDS ImportedModule

================================================================================
