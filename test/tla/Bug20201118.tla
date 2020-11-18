------------ MODULE Bug20201118 ---------------------------
EXTENDS Integers
VARIABLES p, error

AccountIds == { "", "A", "B" }

Data == [
  amount: 0..3
]

Packets == [
  sender: AccountIds,
  data: Data
]

WellFormed(packet) ==
  /\ packet.sender /= ""
  /\ packet.data.amount > 0

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
