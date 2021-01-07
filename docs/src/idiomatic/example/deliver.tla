------------------------------ MODULE deliver ----------------------------------
(*
 * A simple specification of two processes in the network: sender and receiver.
 * The sender sends messages in sequence. The receiver may receive the sent
 * messages out of order, but delivers them to the client in order.
 *
 * Igor Konnov, 2020
 *)

EXTENDS Integers, Apalache

VARIABLES
    sentSeqNo,      \* the sequence number of the next message to be sent
    sent,           \* the messages that are sent by the sender
    received,       \* the messages that are received by the receiver
    deliveredSeqNo  \* the sequence number of the last delivered message

Init ==
    /\ sentSeqNo := 0
    /\ sent := {}
    /\ received := {}
    /\ deliveredSeqNo := -1

Send ==
    /\ sent' := sent \union {sentSeqNo}
    /\ sentSeqNo' := sentSeqNo + 1
    /\ UNCHANGED <<received, deliveredSeqNo>>

Receive ==
    /\ \E msgs \in SUBSET (sent \ received):
        received' := received \union msgs
    /\ UNCHANGED <<sentSeqNo, sent, deliveredSeqNo>>

Deliver ==
    /\ (deliveredSeqNo + 1) \in received
    /\ deliveredSeqNo' := deliveredSeqNo + 1
        \* deliver the message with the sequence number deliveredSeqNo'
    /\ UNCHANGED <<sentSeqNo, sent, received>>

Next ==
    \/ Send
    \/ Receive
    \/ Deliver

Inv ==
    (deliveredSeqNo >= 0) => deliveredSeqNo \in sent
================================================================================
