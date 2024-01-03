---------------------- MODULE TwoPhaseTyped ----------------------------- 
(*
 This specification stems from the specification of the two phase protocol
 by Leslie Lamport:

 https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla

 This specification is annotated with the new Apalache types.
 *)
EXTENDS Integers, FiniteSets, Variants, TwoPhaseTyped_typedefs

\* ANCHOR: constructors
\* @type: $message;
MkCommit == Variant("Commit", "0_OF_NIL")

\* @type: $message;
MkAbort == Variant("Abort", "0_OF_NIL")

\* @type: RM => $message;
MkPrepared(rm) == Variant("Prepared", rm)
\* ANCHOR_END: constructors

\* ANCHOR: constants
CONSTANT
    \* @type: Set(RM);
    RM \* The set of resource managers
\* ANCHOR_END: constants

\* ANCHOR: vars1
VARIABLES
  \* @type: RM -> Str;
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  \* @type: Str;
  tmState,       \* The state of the transaction manager.
  \* @type: Set(RM);
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
\* ANCHOR_END: vars1
\* ANCHOR: vars2
  \* @type: Set($message);
  msgs
\* ANCHOR_END: vars2

\* @type: Set($message);
Message ==
  { MkPrepared(rm): rm \in RM }
    \union
  { MkAbort, MkCommit }

 
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
  /\ tmPrepared   = {}
  /\ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
\* @type: (RM) => Bool;
TMRcvPrepared(rm) ==
  (*************************************************************************)
  (* The TM receives a $"Prepared"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ MkPrepared(rm) \in msgs
  /\ tmPrepared' = tmPrepared \union {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \union { MkCommit }
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \union { MkAbort }
  /\ UNCHANGED <<rmState, tmPrepared>>

\* @type: (RM) => Bool;
RMPrepare(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \union { MkPrepared(rm) }
  /\ UNCHANGED <<tmState, tmPrepared>>
  
\* @type: (RM) => Bool;
RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* @type: (RM) => Bool;
RMRcvCommitMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  /\ MkCommit \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* @type: (RM) => Bool;
RMRcvAbortMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  /\ MkAbort \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

Next ==
  \/ TMCommit \/ TMAbort
  \/ \E rm \in RM : 
      /\ \/ TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)
-----------------------------------------------------------------------------
TPSpec ==
    Init /\ [][Next]_<<rmState, tmState, tmPrepared, msgs>>
  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

\* copied from TCommit
TCConsistent ==
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM :
       ~ /\ rmState[rm1] = "aborted"
         /\ rmState[rm2] = "committed"
==============================================================================

=============================================================================
