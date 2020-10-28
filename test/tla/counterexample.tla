------------------------- MODULE counterexample -------------------------

EXTENDS Config

(* Initial state *)

State1 ==
TRUE
(* Transition 0 to State2 *)

State2 ==
/\ x = 2

(* Transition 0 to State3 *)

State3 ==
/\ x = 4

(* Transition 0 to State4 *)

State4 ==
/\ x = 6

(* Transition 0 to State5 *)

State5 ==
/\ x = 8

(* Transition 0 to State6 *)

State6 ==
/\ x = 10

(* Transition 0 to State7 *)

State7 ==
/\ x = 12

(* Transition 0 to State8 *)

State8 ==
/\ x = 14

(* Transition 0 to State9 *)

State9 ==
/\ x = 16

(* The following formula holds true in the last state and violates the invariant *)

InvariantViolation == x >= 15

================================================================================
\* Created by Apalache on Tue Oct 27 13:14:00 CET 2020
\* https://github.com/informalsystems/apalache
