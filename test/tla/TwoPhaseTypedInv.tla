------------------- MODULE TwoPhaseTypedInv ------------------
EXTENDS TwoPhaseTyped

IndInv ==
    /\ TPTypeOK
    /\ TCConsistent 
    /\ (\E rm \in RM: rmState[rm] = "committed") => tmState = "committed"
    /\ tmState = "committed" => /\ tmPrepared = RM
                                /\ \A rm \in RM: rmState[rm] \notin {"working", "aborted"}
                                /\ MkCommit \in msgs
    /\ tmState = "aborted" => MkAbort \in msgs
    /\ \A rm \in RM:
      /\ rm \in tmPrepared =>
        /\ rmState[rm] /= "working"
        /\ MkPrepared(rm) \in msgs
      /\ rmState[rm] = "working" => MkPrepared(rm) \notin msgs
      /\ MkPrepared(rm) \in msgs => rmState[rm] /= "working" 
      /\ rmState[rm] = "aborted" =>
        \/ MkAbort \in msgs
        \/ MkPrepared(rm) \notin msgs
    /\ MkAbort \in msgs =>
        \* it is either the TM or an RM who was in the "working" state
        \/ tmState = "aborted"
        \/ \E rm \in RM:
          /\ rmState[rm] = "aborted"
          /\ rm \notin tmPrepared
          /\ MkPrepared(rm) \notin msgs                 
    /\ MkCommit \in msgs =>
        /\ tmPrepared = RM
        /\ \/ tmState = "committed"
           \/ \E rm \in RM: rmState[rm] = "committed" 

InitInv ==
    /\ TPTypeOK
    /\ IndInv

==============================================================
