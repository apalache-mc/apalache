------------------------- MODULE counterexample -------------------------

EXTENDS root

(* Initial state *)

State1 ==
TRUE
(* Transition 0 to State2 *)

State2 ==
/\ x = 0

(* Transition 0 to State3 *)

State3 ==
/\ x = 1

(* Transition 0 to State4 *)

State4 ==
/\ x = 2

(* Transition 0 to State5 *)

State5 ==
/\ x = 3

(* The following formula holds true in the last state and violates the invariant *)

InvariantViolation == ~~(x = 3)

================================================================================
\* Created by Apalache on Wed Oct 28 11:25:00 CET 2020
\* https://github.com/informalsystems/apalache
