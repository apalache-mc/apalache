------------------------------- MODULE Unchanged3143 -------------------------------
(*
 * A regression test for issue #3143: "used before assigned" error with
 * grouped-variable UNCHANGED spec. When UNCHANGED uses operator references
 * to tuples of variables (grouped-variable UNCHANGED), the desugarer should
 * properly expand those references.
 *)
VARIABLES
  \* @type: Bool;
  myVar1,
  \* @type: Str;
  myVar2

myList1 == <<myVar1, myVar2>>

VARIABLES
  \* @type: Int;
  myVar3,
  \* @type: Str;
  myVar4

myList2 == <<myVar3, myVar4>>

\* This uses nested operator references, which should be supported.
vars == <<myList1, myList2>>

Init ==
  /\ myVar1 = TRUE
  /\ myVar2 = ""
  /\ myVar3 = 0
  /\ myVar4 = ""

Next == UNCHANGED vars

Spec ==
  /\ Init
  /\ [][Next]_vars

===============================================================================

