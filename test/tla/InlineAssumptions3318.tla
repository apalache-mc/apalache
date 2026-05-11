----------------------- MODULE InlineAssumptions3318 -------------------------
(*
  A regression test for the issue identified in:
  https://github.com/apalache-mc/apalache/issues/3318
*)
EXTENDS Integers

VARIABLE
  \* @type: Int;
  x

ASSUME NamedAssumption == 1 = 1

Init == /\ x = 0
        /\ NamedAssumption

Next == UNCHANGED x

Inv == x = 0

================================================================================
