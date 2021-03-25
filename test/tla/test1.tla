--------------- MODULE test1 -------------
EXTENDS Naturals (*, TLC , Sequences*)
VARIABLE
    \* @type: Set(Int);
    x,
    \* @type: Set(Str);
    y,
    \* @type: Set([a: Int, b: Int, c: Int]);
    z,
    \* @type: Set(Int -> Int);
    w

Init ==
  (*/\ Print("Should find only one distinct state", TRUE)*)
  /\ x = {1, 2, 3}
  /\ y = {"a", "b", "c"}
  /\ z = [a : {1, 2, 3}, b : {1, 2, 3}, c : {1, 2, 3}]
  /\ w = [{1, 2, 3} -> {1, 2, 3}]

Inv  ==
  /\ TRUE
  /\ x = {1, 2, 3}
  /\ y = {"a", "b", "c"}
  /\ z = [a : {1, 2, 3}, b : {1, 2, 3}, c : {1, 2, 3}]
  /\ w = [{1, 2, 3} -> {1, 2, 3}]

Next ==
  \/ /\ x' = {3, 3, 2, 1}
     /\ UNCHANGED <<y, z, w>>
     (*/\ Print("Test 1", TRUE)*)
============================================
