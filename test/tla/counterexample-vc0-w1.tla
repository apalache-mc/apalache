------------------------- MODULE Counterexample -------------------------

\* Transition 0: State 0 to State 1:

ConstInit == TRUE

\* Transition 0: State 0 to State 1:

State1 == a = 1

(* The following formula holds true in State1 and violates the invariant *)
InvariantViolation == TRUE
================================================================================
\* Created Wed Apr 01 22:22:41 CEST 2020 by Apalache
\* https://github.com/konnov/apalache
