------------------------------- MODULE TwoPhaseToUFO ----------------------------- 
(*
 This specification stems from the specification of the two phase protocol
 by Leslie Lamport:

 https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla

 We have modified it for the purposes of testing Apalache.
 *)
EXTENDS Integers, FiniteSets

CONSTANT RM \* The set of resource managers

(* Apalache extensions *)

\*RM == {"r1", "r2", "r3", "r4", "r5", "r6", "r7"}

a <: b == a \* a type annotation

\* a message type
MT == [type |-> STRING, rm |-> STRING]

AsMsg(m) == m <: MT
(* END OF Apalache extensions *)

VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
  msgs           

Message ==
  {[type |-> t, rm |-> r]: t \in {"Prepared"}, r \in RM }
    \cup
  {([type |-> t] <: MT) : t \in {"Commit", "Abort"} }

 
TPTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RM
  /\ msgs \in SUBSET Message

Init ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {} <: {STRING}
  /\ msgs = ({} <: {MT})
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
TMRcvPrepared(rm) ==
  (*************************************************************************)
  (* The TM receives a $"Prepared"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"] <: MT}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"] <: MT}
  /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(rm) == 
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  
RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  /\ ([type |-> "Commit"] <: MT) \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  /\ ([type |-> "Abort"] <: MT) \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

Next ==
  \/ TMCommit \/ TMAbort
  \/ \E rm \in RM : 
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)
-----------------------------------------------------------------------------
TPSpec == Init /\ [][Next]_<<rmState, tmState, tmPrepared, msgs>>
  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

\* copied from TCommit
TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

-----------------------------------------------------------------------------
(* abstraction types to perform abstraction into uninterpreted FOL *)

-------------------- MODULE AbstractionTypes --------------------------------
---- MODULE RmSet ----
(* a set to be translated *)
CONSTANT in_set
(* an uninterpreted set that is modelled with a membership predicate *)
CONSTANT out_in

(* an uninterpreted sort associated with the set members *)
OutType == STRING

AbsTypes ==
    (* shall we use anything more precise than STRING? *)
    out_in \in [OutType -> BOOLEAN]
    
Rule1 ==
    (* what shall we do about P? *)
    (\E rm \in in_set: P) <=> (\E x: out_in[x] /\ P)
======================

---- MODULE TmState ----
(* this is like an abstract data type *)
CONSTANT in_tmState
CONSTANT out_isTmAborted
CONSTANT out_isTmCommitted

OutTypes ==
    /\ out_isTmAborted \in BOOLEAN
    /\ out_isTmCommitted \in BOOLEAN

Rule1 ==
    in_tmState = "init"
        <=> ~out_isTmAborted /\ ~out_isTmCommitted

Rule2 ==
    in_tmState' = "aborted"
        <=> out_isTmAborted' = TRUE /\ out_isTmCommitted' = FALSE

Rule3 ==
    in_tmState' = "committed"
        <=> out_isTmAborted' = FALSE /\ out_isTmCommitted' = TRUE
========================

---- MODULE RmState ----
CONSTANT rmState
CONSTANTS 
  isRmWorking,
  isRmPrepared,
  isRmAborted,
  isRmCommitted

OutTypes ==
    /\ isRmWorking \in [RM -> BOOLEAN]
    /\ isTmPrepared \in [RM -> BOOLEAN]
    /\ isTmAborted \in [RM -> BOOLEAN]
    /\ isTmCommitted \in [RM -> BOOLEAN]

Rule1 ==
    rmState' = fun <=>
      \A rm \in RM:
         /\ fun[rm] = "working" <=> isRmWorking[rm]
         /\ fun[rm] = "prepared" <=> isRmPrepared[rm]
         /\ fun[rm] = "committed" <=> isRmCommitted[rm]
         /\ fun[rm] = "aborted" <=> isRmAborted[rm]
========================

==============================================================================

=============================================================================
