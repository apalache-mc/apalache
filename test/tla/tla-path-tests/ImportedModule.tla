---- MODULE ImportedModule -----------------------------------------------------
(* This trivial MODULE is just to be extended *)

VARIABLES
    \* @type: Bool;
    x

Init ==
    x = TRUE

Next ==
    x' = TRUE

(* Inv == x *)
================================================================================
