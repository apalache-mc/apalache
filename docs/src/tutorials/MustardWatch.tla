---- MODULE MustardWatch -------------------------------------------------------
(* Documentation *)

EXTENDS Naturals

VARIABLES s

Init == s = {x \in {1,3,5,2}: x = 2}

Next == UNCHANGED s

Inv == s = {}

================================================================================
