------------------------ MODULE HandshakeWithTypes ------------------------
(**
 * A TCP-like handshake protocol:
 * https://en.wikipedia.org/wiki/Transmission_Control_Protocol#Connection_establishment
 *
 * Igor Konnov, 2020
 *)
EXTENDS Integers

VARIABLES
    \* @type: Set([syn: Bool, ack: Bool, seqno: Int, ackno: Int]);
    msgs,     \* the set of all messages
    \* @type: Int;
    iseqno,   \* Initiator's sequence number
    \* @type: Int;
    rseqno,   \* Receiver's sequence number
    \* @type: Str;
    istate,   \* Initiator's state
    \* @type: Str;
    rstate    \* Receiver's state

MT == [syn |-> BOOLEAN, ack |-> BOOLEAN, seqno |-> Int, ackno |-> Int]

Init ==
    /\ msgs = {}
    /\ iseqno = 0
    /\ rseqno = 0
    /\ istate = "INIT"
    /\ rstate = "LISTEN"

SendSyn ==
    /\ istate = "INIT"
    /\ \E no \in Nat:
        /\ msgs' = msgs \union {[syn |-> TRUE,
                                 ack |-> FALSE, seqno |-> no]}
        /\ iseqno' = no + 1
        /\ istate' = "SYN-SENT"
        /\ UNCHANGED <<rseqno, rstate>>

SendSynAck ==
    /\ rstate = "LISTEN"
    /\ \E seqno, ackno \in Nat:
        /\ [syn |-> TRUE, ack |-> FALSE, seqno |-> seqno] \in msgs
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
