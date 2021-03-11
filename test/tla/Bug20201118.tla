------------ MODULE Bug20201118 ---------------------------
EXTENDS Integers

VARIABLES
    \* @type: [sender: Str, data: [amount: Int]];
    p,
    \* @type: Bool;
    error

AccountIds == { "", "A", "B" }

Data == [
  amount: 0..3
]

Packets == [
  sender: AccountIds,
  data: Data
]

\* @type: [sender: Str, data: [amount: Int]] => Bool;
WellFormed(packet) ==
  /\ packet.sender /= ""
  /\ packet.data.amount > 0

\* @type: [sender: Str, data: [amount: Int]] => Bool;
Pre(packet) ==
  LET data == packet.data IN
  WellFormed(packet)

Init ==
  /\ p \in Packets
  /\ error = FALSE

Action(packet) ==
  \/ /\ error' = FALSE
     /\ Pre(packet)
  \/ /\ error' = TRUE
     /\ ~Pre(packet)

Next ==
  /\ p' \in Packets
  /\ Action(p')

Inv == (error = TRUE) =>
        (p.data.amount <= 0 \/ p.sender = "")
===========================================================
