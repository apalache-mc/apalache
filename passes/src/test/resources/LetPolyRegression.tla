---- MODULE LetPolyRegression ----
EXTENDS Integers

Direct(n) == n + 1
ViaLet(n) == LET k == n + 1 IN k
ViaLetIf(n) == LET a == IF n < 0 THEN -n ELSE n IN a
ViaLocal(n) == LET G(y) == y + n IN G(1)
ViaNested(n) == LET k == LET j == n + 1 IN j IN k
====
