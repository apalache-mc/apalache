------------------------------ MODULE TestGen ---------------------------------
(* A simple test for the data structure generator *)
EXTENDS Integers, Apalache

VARIABLES
    (*
     @typeAlias: MSG = [seqno: Int, ballot: Int];
     @type: Set(MSG);
    *)
    msgs,
    \* @type: Int;
    seqno

\* preparing a test, like you do it in unit tests
Before ==
    /\ seqno = Gen(1)
    /\ msgs = Gen(5)
    /\ \A m \in msgs:
        m.seqno < seqno

\* run the test (typically, an action)
Test ==
    /\ \E b \in Int:
        msgs' = { [seqno |-> seqno, ballot |-> b] } \union msgs
    /\ seqno' = seqno + 1    

\* check the expectation after running the test
After ==
    \A m1, m2 \in msgs:
      m2.seqno > m1.seqno => m2.ballot >= m1.ballot

===============================================================================
