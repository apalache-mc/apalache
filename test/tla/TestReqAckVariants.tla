----------------------- MODULE TestReqAckVariants ------------------------------
\* A test for the Variants module.
\* This test should work when ADR-014 is implemented.

EXTENDS Integers, Sequences, Variants

Amounts == 1..10

VARIABLES
    \* @type: Int;
    balance,
    (*
      @typeAlias: MESSAGE = Req({ ask: Int }) | Ack({ success: Bool });

      @type: Set(MESSAGE);
     *)
    msgs,
    (*
      @typeAlias: EVENT = Withdraw(Int) | Lacking(Int);

      @type: Seq(EVENT);  
     *)
    log

Init ==
    /\ balance = 100
    /\ msgs = {}
    /\ log = << >>

SendRequest(ask) ==
    /\ ask > 0
    /\ LET \* @type: MESSAGE;
           m == Variant("Req", [ ask |-> ask ]) IN
       msgs' = msgs \union { m }
    /\ UNCHANGED <<balance, log>>


ProcessRequest(ask) ==
    /\  IF balance >= ask
        THEN LET \* @type: EVENT;
                 entry == Variant("Withdraw", ask) IN
             LET \* @type: MESSAGE;
                 ack == Variant("Ack", [ success |-> TRUE ]) IN
            /\ balance' = balance - ask
            /\ log' = Append(log, entry)
            /\ msgs' = (msgs \ { Variant("Req", [ ask |-> ask]) }) \union { ack }
        ELSE LET \* @type: EVENT;
                 entry == Variant("Lacking", ask - balance) IN
             LET \* @type: MESSAGE;
                 ack == Variant("Ack", [ success |-> FALSE ]) IN
            /\ log' = Append(log, entry)
            /\ msgs' = (msgs \ { Variant("Req", [ ask |-> ask]) }) \union { ack }
            /\ UNCHANGED balance


Next ==
    \/ \E ask \in Amounts:
        SendRequest(ask)
    \/ \E m \in VariantFilter("Req", msgs):
        ProcessRequest(m.ask)

===============================================================================
