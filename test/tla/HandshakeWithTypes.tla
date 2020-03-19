------------------------ MODULE HandshakeWithTypes ------------------------
(**
 * A TCP-like handshake protocol:
 * https://en.wikipedia.org/wiki/Transmission_Control_Protocol#Connection_establishment
 *
 * Igor Konnov, 2020
 *)
EXTENDS Integers

VARIABLES msgs,     \* the set of all messages
          iseqno,   \* Initiator's sequence number
          rseqno,   \* Receiver's sequence number
          istate,   \* Initiator's state
          rstate    \* Receiver's state

a <: b == a

MT == [syn |-> BOOLEAN, ack |-> BOOLEAN, seqno |-> Int, ackno |-> Int]

Init ==
    /\ msgs = {} <: {MT}
    /\ iseqno = 0
    /\ rseqno = 0
    /\ istate = "INIT"
    /\ rstate = "LISTEN"

SendSyn ==
    /\ istate = "INIT"
    /\ \E no \in Nat:
        /\ msgs' = msgs \union {[syn |-> TRUE,
                                 ack |-> FALSE, seqno |-> no] <: MT}
        /\ iseqno' = no + 1
        /\ istate' = "SYN-SENT"
        /\ UNCHANGED <<rseqno, rstate>>

SendSynAck ==
    /\ rstate = "LISTEN"
    /\ \E seqno, ackno \in Nat:
        /\ ([syn |-> TRUE, ack |-> FALSE, seqno |-> seqno] <: MT) \in msgs
        /\ msgs' = msgs \union {[syn |-> TRUE, ack |-> TRUE,
                                 seqno |-> seqno + 1,
                                 ackno |-> ackno]}
        /\ rseqno' = ackno + 1
        /\ rstate' = "SYN-RECEIVED"
        /\ UNCHANGED <<iseqno, istate>>

SendAck ==
    /\ istate = "SYN-SENT"
    /\ \E ackno \in Nat:
        /\ [syn |-> TRUE, ack |-> TRUE,
            seqno |-> iseqno, ackno |-> ackno] \in msgs
        /\ istate' = "ESTABLISHED"
        /\ msgs' = msgs \union {[syn |-> FALSE, ack |-> TRUE,
                                 seqno |-> iseqno,
                                 ackno |-> ackno + 1]}
        /\ UNCHANGED <<iseqno, rseqno, rstate>>

RcvAck ==
    /\ rstate = "SYN-RECEIVED"
    /\ \E seqno \in Nat:
        /\ ([syn |-> FALSE, ack |-> TRUE,
             seqno |-> seqno, ackno |-> rseqno]) \in msgs
        /\ rstate' = "ESTABLISHED"
        /\ UNCHANGED <<msgs, iseqno, rseqno, istate>>


Next == SendSyn \/ SendSynAck \/ SendAck \/ RcvAck

Inv == (rstate = "ESTABLISHED" => istate = "ESTABLISHED")

======================================================================
