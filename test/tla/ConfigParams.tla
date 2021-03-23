--------------------------- MODULE ConfigParams -------------------------------
CONSTANTS
  \* @type: Int;
  MyInt,
  \* @type: Str;
  MyStr,
  \* TODO: use a model type here
  \* when #570 is closed: https://github.com/informalsystems/apalache/issues/570
  \* @type: Str;
  MyModelValue1,
  \* @type: Str;
  MyModelValue2,
  \* @type: Set(Int);
  MySet

VARIABLES
  \* @type: Int;
  x,
  \* @type: Str;
  y,
  \* @type: Str;
  z,
  \* @type: Set(Int);
  w

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
