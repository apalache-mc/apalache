---- MODULE LetSharedTypes ----
EXTENDS Integers

F(n) == LET k == (CHOOSE y \in {n}: TRUE) = n
            c == n + 1
        IN k /\ c > 0

Reversed(n) == LET c == n + 1
                   k == (CHOOSE y \in {n}: TRUE) = n
               IN k /\ c > 0

ViaBody(n) == LET k == (CHOOSE y \in {n}: TRUE) = n
             IN k /\ n > 0

Nested(n) == LET k == LET j == CHOOSE y \in {n}: TRUE IN j
            IN k + 1

Alias(n, m) == LET k == IF TRUE THEN n ELSE m
                  c == m + 1
              IN k + c

ViaSet(n) == LET k == n \cup {} IN k \cup {1}

ViaRecord(n) == LET k == [captured |-> n]
                   c == n + 1
               IN k.captured + c

VARIABLE
  \* @type: Bool;
  x

Init == x = (F(1) /\ Reversed(1) /\ ViaBody(1) /\ Nested(1) = 2
             /\ Alias(1, 1) = 3 /\ ViaSet({}) = {1} /\ ViaRecord(1) = 3)
Next == UNCHANGED x
Inv == x
====
