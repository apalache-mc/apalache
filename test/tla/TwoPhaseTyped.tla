---------------------- MODULE TwoPhaseTyped ----------------------------- 
(*
 This specification stems from the specification of the two phase protocol
 by Leslie Lamport:

 https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla

 This specification is annotated with the new Apalache types.
 *)
EXTENDS Integers, FiniteSets, Typing

CONSTANT
    \* type: RM
    RM \* The set of resource managers

VARIABLES
  \* type: RM -> Str
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  \* type: Str
  tmState,       \* The state of the transaction manager.
  \* type: Set(RM)
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
  \* type: Set([type: Str, rm: RM])
  msgs           

\* We should have at most one such axiom per spec, to avoid collisions.
\* This axiom is similar to TypeOK. It should always be a conjunction 
TypeAssumptions ==
  \* RMT is a global type name, as it is in CamelCase
  /\ AssumeType(RM, "Set(RM)")
  /\ AssumeType(rmState, "RM -> Str")
  /\ AssumeType(tmState, "Str")
  /\ AssumeType(tmPrepared, "Set(RM)")
  /\ AssumeType(msgs, "Set([type: Str, rm: RM])")

Message == \*"Set([type: Str, rm: RM])" :>
  {[type |-> t, rm |-> r]: t \in {"Prepared"}, r \in RM }
    \cup
  {[type |-> t] : t \in {"Commit", "Abort"} }

 
TPTypeOK == \*"() => Bool" :>
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RM
  /\ msgs \in SUBSET Message

Init == \*"() => Bool" :>
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
TMRcvPrepared(rm) == \*"(RM) => Bool" :>
  (*************************************************************************)
  (* The TM receives a $"Prepared"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit == \*"() => Bool" :>
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort == \*"() => Bool" :>
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(rm) ==  \*"(RM) => Bool" :>
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  
RMChooseToAbort(rm) == \*"(RM) => Bool" :>
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(rm) == \*"(RM) => Bool" :>
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(rm) == \*"(RM) => Bool" :>
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

Next == \*"() => Bool" :>
  \/ TMCommit \/ TMAbort
  \/ \E rm \in RM : 
      /\ \/ TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)
-----------------------------------------------------------------------------
TPSpec == \*"() => Bool" :>
    Init /\ [][Next]_<<rmState, tmState, tmPrepared, msgs>>
  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

\* copied from TCommit
TCConsistent ==  \*"() => Bool" :>
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM :
       ~ /\ rmState[rm1] = "aborted"
         /\ rmState[rm2] = "committed"
==============================================================================

=============================================================================
