---- MODULE View2 ----
EXTENDS Integers
VARIABLES
    \* @type: Int;
    x

Init ==
  x = 0

A ==
  x' = x + 1

B ==
  x' = x - 1

C ==
  x' = x

Next ==
  A \/ B \/ C

Inv ==
  x = 0

\* @type: <<Bool, Bool>>;
View1 ==
  <<x < 0, x > 0>>
=================
