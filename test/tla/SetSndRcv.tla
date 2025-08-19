---------------------------- MODULE SetSndRcv --------------------------
\* A regression test for the use of oracles in set minus, see:
\* https://github.com/apalache-mc/apalache/issues/1152

\* We model message transmission from sender to receiver via transmission medium.
\* The medium models lossy transmission, i.e., it can drop messages.
\* The goal is to send messages from sender to receiver, and not to lose all of them.
\* The invariant specifies that sender, receiver, and medium are not empty.
\* The erroneous state can be reached in 2*N steps for N messages.
\*
\* Andrey Kuprianov and Shon Feder, 2021

EXTENDS FiniteSets, Naturals

CONSTANT
  \* @type: Set(Int);
  Values

VARIABLE
  \* @type: Set(Int);
  sender,
  \* @type: Set(Int);
  receiver,
  \* @type: Set(Int);
  medium

CInit == Values = 0..6

Init ==
  /\ sender = Values
  /\ receiver = {}
  /\ medium = {}

Snd ==
  \E x \in sender :
    /\ sender' = sender \ {x}
    /\ medium' = medium \union {x}
    /\ UNCHANGED(<<receiver>>)

Drop ==
  \E x \in medium :
    /\ medium' = medium \ {x}
    /\ UNCHANGED(<<sender, receiver>>)

\* On receive, we do not remove the message from the medium;
\* this is both natural (multiple copies can be in transit),
\* and makes model checking harder (more states to consider)
Rcv ==
  \E x \in medium :
    /\ receiver' = receiver \union {x}
    /\ UNCHANGED(<<sender, medium>>)

Next ==
  \/ Snd
  \/ Drop
  \/ Rcv

Inv ==
  \/ sender /= {}
  \/ medium /= {}
  \/ receiver /= {}

=============================================================================
