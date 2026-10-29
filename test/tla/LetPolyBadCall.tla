---- MODULE LetPolyBadCall ----
EXTENDS Integers

ViaLet(n) == LET k == n + 1 IN k

VARIABLE
  \* @type: Int;
  x

Init == x = ViaLet({TRUE})
====
