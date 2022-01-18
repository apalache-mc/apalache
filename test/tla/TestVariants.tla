--------------------------- MODULE TestVariants -------------------------------
\* A test for the Variants module.
\* This test should work when ADR-014 is implemented.

EXTENDS Integers, Sequences, Variants

Amounts == 1..10

VARIABLES
    \* @type: Int;
    balance,
    (*
      @typeAlias: MESSAGE =
          [ tag: "req", ask: Int ]
        | [ tag: "ack", success: Bool ];
      @type: Set(MESSAGE);
     *)
    msgs,
    (*
      @typeAlias: EVENT =
          [ tag: "withdraw", amount: Int ]
        | [ tag: "lacking", amount: Int ];
      @type: Seq(EVENT);  
     *)
    log

Init ==
    /\ balance = 100
    /\ msgs = {}
    /\ log = << >>

SendRequest(ask) ==
    /\ ask > 0
    /\ LET m == Variant([ tag |-> "req", ask |-> ask ]) IN
       msgs' = msgs \union { m }
    /\ UNCHANGED <<balance, log>>


ProcessRequest(m) ==
    /\  IF balance >= m.ask
        THEN LET entry == Variant([ tag |-> "withdraw", amount |-> m.ask ]) IN
             LET ack == Variant([ tag |-> "ack", success |-> TRUE ]) IN
            /\ balance' = balance - m.ask
            /\ log' = Append(log, entry)
            /\ msgs' = (msgs \ { m }) \union { ack }
        ELSE LET entry ==
                Variant([ tag |-> "lacking", amount |-> m.ask - balance ]) IN
             LET ack == Variant([ tag |-> "ack", success |-> FALSE ]) IN
            /\ log' = Append(log, entry)
            /\ msgs' = (msgs \ { m }) \union { ack }
            /\ UNCHANGED balance


Next ==
    \/ \E ask \in Amounts:
        SendRequest(ask)
    \/ \E m \in FilterByTag(msgs, "req"):
        ProcessRequest(m)

===============================================================================
