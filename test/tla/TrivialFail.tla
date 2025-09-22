------ MODULE TrivialFail ------
(* A spec which can always advance but with an invariant that always fails.

   Introduced to address https://github.com/apalache-mc/apalache/issues/2158 *)

Init == TRUE
Next == TRUE
Inv == FALSE
================================
