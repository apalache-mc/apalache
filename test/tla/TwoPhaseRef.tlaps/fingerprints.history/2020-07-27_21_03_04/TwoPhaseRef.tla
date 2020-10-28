--------------------------- MODULE TwoPhaseRef ----------------------------- 
(*
  That is how refinement proofs for TwoPhase may look like.

  Igor Konnov, 2020
 *)

CONSTANT RM

VARIABLES tmState, rmState, msgs, tmPrepared

C == INSTANCE TwoPhase

(* mapping a concrete state on an abstract state *)
rmWorking == [rm \in RM |-> rmState[rm] = "working"]

rmPrepared == [rm \in RM |-> rmState[rm] = "prepared"]

rmCommitted == [rm \in RM |-> rmState[rm] = "committed"]

rmAborted == [rm \in RM |-> rmState[rm] = "aborted"]

sentPrepared == [rm \in RM |-> [type |-> "Prepared", rm |-> rm] \in msgs]

A == INSTANCE TwoPhaseUFO

\* is it hard to prove these theorems with TLAPS?

THEOREM C!Init => A!Init
  <1> SUFFICES ASSUME C!Init
               PROVE  A!Init
    OBVIOUS
  <1>1. \A rm \in RM: rmWorking[rm] = TRUE
   <2>1. TAKE r \in RM
   <2>2. rmState[r] = "working" /\ rmWorking[r] = TRUE 
    BY DEF C!Init, rmWorking
   <2>4. QED BY <2>1, <2>2
  <1>2. \A rm \in RM: ~rmPrepared[rm]
   <2>1. TAKE r \in RM
   <2>2. rmState[r] /= "prepared" /\ ~rmPrepared[r]
     BY DEF C!Init, rmPrepared
   <2>3. QED BY <2>1, <2>2
  <1>3. \A rm \in RM: ~rmCommitted[rm]
   <2>1. TAKE r \in RM
   <2>2. rmState[r] /= "committed" /\ ~rmCommitted[r]
     BY DEF C!Init, rmCommitted 
   <2>3. QED BY <2>1, <2>2
  <1>4. \A rm \in RM: ~rmAborted[rm]
   <2>1. TAKE r \in RM
   <2>2. rmState[r] /= "aborted" /\ ~rmAborted[r]
     BY DEF C!Init, rmAborted
   <2>3. QED BY <2>1, <2>2  
  <1>5. \A rm \in RM: sentPrepared[rm] = FALSE
   <2>1. TAKE r \in RM
   <2>2. msgs = {} /\ ~sentPrepared[r]
     BY DEF C!Init, C!<:, sentPrepared
   <2>3. QED BY <2>1, <2>2
  <1>6. tmState = "init"
     BY DEF C!Init
  <1>7. A!Init = TRUE
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF A!Init
  <1>8. QED
    BY <1>7

THEOREM \A rm \in RM: C!TMRcvPrepared(rm) => A!TMRcvPrepared(rm)

THEOREM C!TMCommit => A!TMCommit

THEOREM C!TMAbort => A!TMAbort

THEOREM \A rm \in RM: C!RMPrepare(rm) => A!RMPrepare(rm)

THEOREM \A rm \in RM: C!RMChooseToAbort(rm) => A!RMChooseToAbort(rm)

THEOREM \A rm \in RM: C!RMRcvCommitMsg(rm) => A!RMRcvCommitMsg(rm)

THEOREM \A rm \in RM: C!RMRcvAbortMsg(rm) => A!RMRcvAbortMsg(rm)

THEOREM \A rm \in RM: C!Next => A!Next

THEOREM \A rm \in RM: C!TCConsistent => A!TCConsistent

=============================================================================
