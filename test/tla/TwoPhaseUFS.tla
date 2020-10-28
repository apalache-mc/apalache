------------------------------- MODULE TwoPhaseUFS3 ----------------------------- 
(*
  Two-phase commit in uninterpreted first-order logic,
  somewhat following the IVy methodology but in TLA+.
  It is an abstraction of TwoPhase. In this model,
  we are using the set RM.

  Igor Konnov, 2020
 *)

\*CONSTANT RM \* The set of resource managers

(* Apalache extensions *)

RM == {"r1", "r2", "r3"}

\*a <: b == a \* a type annotation

\* a message type
\*MT == [type |-> STRING, rm |-> STRING]

\*AsMsg(m) == m <: MT
(* END OF Apalache extensions *)

VARIABLES
  rmWorking,        \* is a resource manager working
  rmPrepared,       \* has been a resource manager prepared
  rmCommitted,      \* has a resource manager committed
  rmAborted,        \* has a resource manager aborted
  sentPrepared,     \* has a resource manager sent a "Prepared" message
  tmState           \* The state of the transaction manager.

(*
Message ==
  {[type |-> t, rm |-> r]: t \in {"Prepared"}, r \in RM }
    \cup
  {([type |-> t] <: MT) : t \in {"Commit", "Abort"} }
 *)

 
(*
TPTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RM
  /\ msgs \in SUBSET Message
*)

Init ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ \A rm: rmWorking[rm] = TRUE
  /\ \A rm: rmPrepared[rm] = FALSE
  /\ \A rm: rmCommitted[rm] = FALSE
  /\ \A rm: rmAborted[rm] = FALSE
  /\ \A rm: sentPrepared[rm] = FALSE
  /\ tmState = "init"
  (*
  /\ tmPrepared   = {} <: {STRING}
  /\ msgs = ({} <: {MT})
  *)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
TMRcvPrepared(rm) ==
  (*************************************************************************)
  (* The TM receives a $"Prepared"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  \* in the abstraction, this action does not nothing, but we keep it
  /\ tmState = "init"
  /\ UNCHANGED <<rmWorking, rmPrepared, rmCommitted, rmAborted, sentPrepared, tmState>>
(*
  \* concrete code:

  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>
  *)

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmState = "init"
  \* /\ tmPrepared = RM
  /\ \A rm: sentPrepared[rm]
  /\ tmState' = "committed"
  \* /\ msgs' = msgs \cup {[type |-> "Commit"] <: MT}
  /\ UNCHANGED <<rmWorking, rmPrepared, rmCommitted, rmAborted, sentPrepared>>

TMAbort ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "aborted"
  \*/\ msgs' = msgs \cup {[type |-> "Abort"] <: MT}
  /\ UNCHANGED <<rmWorking, rmPrepared, rmCommitted, rmAborted, sentPrepared>>

RMPrepare(rm) == 
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  /\ rmWorking[rm]
  \*/\ rmState[rm] = "working"
  /\ rmWorking' = [rmWorking EXCEPT ![rm] = FALSE]
  /\ rmPrepared' = [rmPrepared EXCEPT ![rm] = TRUE]
  \*/\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ sentPrepared' = [sentPrepared EXCEPT ![rm] = TRUE]
  \*/\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<rmCommitted, rmAborted, tmState>>
  
RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmWorking[rm]
  \*/\ rmState[rm] = "working"
  /\ rmWorking' = [rmWorking EXCEPT ![rm] = FALSE]
  /\ rmAborted' = [rmAborted EXCEPT ![rm] = TRUE]
  \*/\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<rmPrepared, rmCommitted, sentPrepared, tmState>>

RMRcvCommitMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  /\ tmState = "committed"
  \*/\ ([type |-> "Commit"] <: MT) \in msgs
  /\ rmWorking' = [rmWorking EXCEPT ![rm] = FALSE]
  /\ rmPrepared' = [rmPrepared EXCEPT ![rm] = FALSE]
  /\ rmCommitted' = [rmCommitted EXCEPT ![rm] = TRUE]
  /\ rmAborted' = [rmAborted EXCEPT ![rm] = FALSE]
  \*/\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<sentPrepared, tmState>>

RMRcvAbortMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  /\ tmState = "aborted"
  \*/\ ([type |-> "Abort"] <: MT) \in msgs
  /\ rmWorking' = [rmWorking EXCEPT ![rm] = FALSE]
  /\ rmPrepared' = [rmPrepared EXCEPT ![rm] = FALSE]
  /\ rmCommitted' = [rmCommitted EXCEPT ![rm] = FALSE]
  /\ rmAborted' = [rmAborted EXCEPT ![rm] = TRUE]
  \*/\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<sentPrepared, tmState>>

Next ==
  \/ TMCommit \/ TMAbort
  \/ \E rm (*\in RM*) : 
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)
-----------------------------------------------------------------------------
\*TPSpec == Init /\ [][Next]_<<rmState, tmState, tmPrepared, msgs>>
  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

\* copied from TCommit
TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2: ~(rmAborted[rm1] /\ rmCommitted[rm2])
  (*
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"
   *)

=============================================================================
