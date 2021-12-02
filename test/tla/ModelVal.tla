---------- MODULE ModelVal ----------

EXTENDS Integers

CONSTANT 
  \* @type: UT;
  C,
  \* @type: XY;
  G

VARIABLE
  \* @type: Set(UT);
  x,
  \* @type: Set(XY);
  z,
  \* @type: Str;
  s

CInit == C = "1_OF_UT" /\ G = "1_OF_XY"

Init == x = {} /\ z = {G} /\ s = "init"

Next == x' = {C} /\ z' = {} /\ s' = "next"

Inv == G \in z \/ C \in x
====================
