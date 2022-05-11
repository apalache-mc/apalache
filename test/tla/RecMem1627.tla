----------------------- MODULE RecMem1627 ----------------------------
EXTENDS Integers

VARIABLES 
  \* @type: { pos: Int, q: Int, color: Str };
  token       \* token structure

N == 3
Node == 0 .. N-1
Color == {"white", "black"}
Token == [pos : Node, q : Int, color : Color]

TypeOK ==
  token \in Token

Init ==
  token = [pos |-> 0, q |-> 0, color |-> "black"]

Next ==
  UNCHANGED token

=====================================================================  
