--------------------------- MODULE ConfigParams -------------------------------
CONSTANTS
  MyInt,
  MyStr,
  MyModelValue1,
  MyModelValue2,
  MySet

VARIABLES
  x, y, z, w

Init ==
    /\ x = MyInt
    /\ y = MyStr
    /\ z = MyModelValue1
    /\ w = MySet

Next ==
    UNCHANGED <<x, y, z, w>>

Inv ==
    /\ x = 42
    /\ y = "hello"
    /\ z = MyModelValue1
    /\ z /= MyModelValue2
    /\ w = { 1, 2, 3 }

===============================================================================
