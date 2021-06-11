---- MODULE View ----
EXTENDS Integers, Sequences
VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y,
    \* @type: Str;
    action

Init ==
  /\ x = 0
  /\ y = 0
  /\ action = "Init"

A ==
  \E d \in Int:
    /\ x' = x + d
    /\ y' = y
    /\ action' = "A"

B ==
  \E d \in Int:
    /\ x' = x
    /\ y' = y + d
    /\ action' = "B"

Next ==
  A \/ B

Inv ==
  x + y < 10

\* @type: <<Bool, Bool>>;
View1 ==
  <<x >= 0, y >= 0>>

View2 ==
  action

\* @type: Seq([x: Int, y: Int, action: Str]) => Bool;
TraceInv1(hist) ==
  \/ /\ hist[1].x = 0 /\ hist[1].y = 0
     /\ hist[2].x = 10 /\ hist[2].y = 0
  \/ LET last == hist[Len(hist)] IN
     last.x + last.y < 10

\* @type: Seq([x: Int, y: Int, action: Str]) => Bool;
TraceInv2(hist) ==
  \/ /\ hist[1].x >= 0 /\ hist[1].y >= 0
     /\ hist[2].x >= 0 /\ hist[2].y >= 0
  \/ LET last == hist[Len(hist)] IN
     last.x + last.y < 10

\* @type: Seq([x: Int, y: Int, action: Str]) => Bool;
TraceInv3(hist) ==
  \/ /\ hist[1].x >= 0 /\ hist[1].y >= 0
     /\ hist[2].x >= 0 /\ hist[2].y >= 0
  \/ /\ hist[1].x >= 0 /\ hist[1].y >= 0
     /\ hist[2].x < 0  /\ hist[2].y >= 0
     /\ hist[3].x >= 0 /\ hist[3].y >= 0
  \/ LET last == hist[Len(hist)] IN
     last.x + last.y < 10
=================
