---------------------- MODULE TwoPhaseUFO ----------------------------- 
(*
 This specification stems from the specification of the two phase protocol
 by Leslie Lamport:

 https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla

 We rewrite TwoPhase in uninterpreted first-order logic, which is a fragment of
 TLA+.
 *)

CONSTANT
    \* We define the set of all values of the sort SORT_RM,
    \* as we are quantifying over this sort.
    \* @type: Set(SORT_RM);
    Values_RM

VARIABLES
  \* rmState[rm] is the state of resource manager RM.
  \* It is an uninterpreted non-Boolean function, which is fine in UFOL.
  \* @type: SORT_RM -> SORT_STATE;
  rmState,
  \* The state of the transaction manager.
  \* It is simply an uninterpreted constant.
  \* @type: SORT_STATE;
  tmState,       \* The state of the transaction manager.
  \* The set of RMs from which the TM has received 'Prepared'
  \* messages, which is expressed as a predicate in UFOL.
  \* @type: SORT_RM -> Bool;
  tmPrepared,    
  \* Three predicates, one per message type.
  \* In contrast to the original specification, we have to partition
  \* message types into three subsets, which are modelled as predicates.

  \* messages of the type 'Prepared'
  \* @type: SORT_RM -> Bool;
  msgsPrepared,
  \* messages of the type 'Commit'
  \* @type: Bool;
  msgsCommit,
  \* messages of the type 'Abort'
  \* @type: Bool;
  msgsAbort

\* We do not need this definition in UFOL:
(*
Message ==
  ({[type |-> t, rm |-> r]: t \in {"Prepared"}, r \in RM }
   \union
   {[type |-> t] : t \in {"Commit", "Abort"}})
*)
 
\* We do not need this definition in UFOL:
\*TPTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
(*  
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RM
  /\ msgs \in SUBSET Message
 *) 

Init ==
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  \* working_OF_SORT_STATE is interpreted
  \* as a distinct constant 'working' of the sort SORT_STATE
  /\ rmState = [rm \in Values_RM |-> "working_OF_SORT_STATE"]
  /\ tmState = "init_OF_SORT_STATE"
  \*/\ tmPrepared   = {}
  /\ tmPrepared = [rm \in Values_RM |-> FALSE]
  \*/\ msgs = {}
  /\ msgsPrepared = [rm \in Values_RM |-> FALSE]
  /\ msgsCommit = FALSE
  /\ msgsAbort = FALSE

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
\* @type: (SORT_RM) => Bool;
TMRcvPrepared(rm) ==
  (*************************************************************************)
  (* The TM receives a $"Prepared"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  /\ tmState = "init_OF_SORT_STATE"
  \*/\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ msgsPrepared[rm]
  \*/\ tmPrepared' = tmPrepared \union {rm}
  /\ tmPrepared' = [ tmPrepared EXCEPT ![rm] = TRUE ]
  /\ UNCHANGED <<rmState, tmState, msgsPrepared, msgsCommit, msgsAbort>>

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmState = "init_OF_SORT_STATE"
  \*/\ tmPrepared = RM
  /\ \A rm \in Values_RM:
        tmPrepared[rm]
  /\ tmState' = "committed_OF_SORT_STATE"
  \*/\ msgs' = msgs \union {[type |-> "Commit"]}
  /\ msgsCommit' = TRUE
  /\ UNCHANGED <<rmState, tmPrepared, msgsPrepared, msgsAbort>>

TMAbort ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init_OF_SORT_STATE"
  /\ tmState' = "aborted_OF_SORT_STATE"
  \*/\ msgs' = msgs \union {[type |-> "Abort"]}
  /\ msgsAbort' = TRUE
  /\ UNCHANGED <<rmState, tmPrepared, msgsPrepared, msgsCommit>>

\* @type: (SORT_RM) => Bool;
RMPrepare(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  /\ rmState[rm] = "working_OF_SORT_STATE"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared_OF_SORT_STATE"]
  \*/\ msgs' = msgs \union {[type |-> "Prepared", rm |-> rm]}
  /\ msgsPrepared' = [ msgsPrepared EXCEPT ![rm] = TRUE ]
  /\ UNCHANGED <<tmState, tmPrepared, msgsAbort, msgsCommit>>
  
\* @type: (SORT_RM) => Bool;
RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmState[rm] = "working_OF_SORT_STATE"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted_OF_SORT_STATE"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>

\* @type: (SORT_RM) => Bool;
RMRcvCommitMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  \*/\ [type |-> "Commit"] \in msgs
  /\ msgsCommit
  /\ rmState' = [rmState EXCEPT ![rm] = "committed_OF_SORT_STATE"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>

\* @type: (SORT_RM) => Bool;
RMRcvAbortMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  \*/\ [type |-> "Abort"] \in msgs
  /\ msgsAbort
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted_OF_SORT_STATE"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>

Next ==
  \/ TMCommit \/ TMAbort
  \*\/ \E rm \in RM : 
  \/ \E rm \in Values_RM : 
      /\ \/ TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)
-----------------------------------------------------------------------------
TPSpec ==
    Init /\
      [][Next]_<<rmState, tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>
  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

\* copied from TCommit
TCConsistent ==
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \*\A rm1, rm2 \in RM :
  \A rm1, rm2 \in Values_RM :
       ~ /\ rmState[rm1] = "aborted_OF_SORT_STATE"
         /\ rmState[rm2] = "committed_OF_SORT_STATE"
==============================================================================

=============================================================================
