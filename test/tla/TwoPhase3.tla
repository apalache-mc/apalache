------------------------------- MODULE TwoPhase3 ----------------------------- 
(***************************************************************************)
(* This specification describes the Two-Phase Commit protocol, in which a  *)
(* transaction manager (TM) coordinates the resource managers (RMs) to     *)
(* implement the Transaction Commit specification of module $TCommit$.  In *)
(* this specification, RMs spontaneously issue $Prepared$ messages.  We    *)
(* ignore the $Prepare$ messages that the TM can send to the               *)
(* RMs.\vspace{.4em}                                                       *)
(*                                                                         *)
(* For simplicity, we also eliminate $Abort$ messages sent by an RM when   *)
(* it decides to abort.  Such a message would cause the TM to abort the    *)
(* transaction, an event represented here by the TM spontaneously deciding *)
(* to abort.\vspace{.4em}                                                  *)
(*                                                                         *)
(* This specification describes only the safety properties of the          *)
(* protocol--that is, what is allowed to happen.  What must happen would   *)
(* be described by liveness properties, which we do not specify.           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

\*CONSTANT RM \* The set of resource managers
RM == { "r1", "r2", "r3" }

(* BMCMT extensions *)

\*ConstInit3 == RM \in {{ "r1", "r2", "r3" }}
\*ConstInit7 == RM \in {{"r1", "r2", "r3", "r4", "r5", "r6", "r7"}}

\*ConstInit ==
\*    /\ \E N \in 1..20: RM \in {{ i \in 1..20: i <= N }}
\*    /\ \E r1, r2 \in RM: r1 /= r2 \* there are at least two elements

a <: b == a \* a type annotation

\* new: a message type
MT == [type |-> STRING, rm |-> STRING]
(* END OF BMCMT extensions *)

VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
  msgs           
    (***********************************************************************)
    (* In the protocol, processes communicate with one another by sending  *)
    (* messages.  Since we are specifying only safety, a process is not    *)
    (* required to receive a message, so there is no need to model message *)
    (* loss.  (There's no difference between a process not being able to   *)
    (* receive a message because the message was lost and a process simply *)
    (* ignoring the message.)  We therefore represent message passing with *)
    (* a variable $msgs$ whose value is the set of all messages that have  *)
    (* been sent.  Messages are never removed from $msgs$.  An action      *)
    (* that, in an implementation, would be enabled by the receipt of a    *)
    (* certain message is here enabled by the existence of that message in *)
    (* $msgs$.  (Receipt of the same message twice is therefore allowed;   *)
    (* but in this particular protocol, receiving a message for the second *)
    (* time has no effect.)                                                *)
    (***********************************************************************)

Message ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type $"Prepared"$ are  *)
  (* sent from the RM indicated by the message's $rm$ field to the TM\@.   *)
  (* Messages of type $"Commit"$ and $"Abort"$ are broadcast by the TM, to *)
  (* be received by all RMs.  The set $msgs$ contains just a single copy   *)
  (* of such a message.                                                    *)
  (*************************************************************************)
  (*[type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]*)

  {[type |-> t, rm |-> r]: t \in {"Prepared"}, r \in RM }
    \cup
  {([type |-> t] <: MT) : t \in {"Commit", "Abort"} }
  \*[type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]

(*
InitInv ==  
  /\ ConstInit7
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RM
  /\ msgs \in SUBSET Message
  \* copied from TCConsistent
  /\ \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                            /\ rmState[rm2] = "committed"
  \* copied from Inv, just use Inv, when Jure fixes the bug
  /\ (\E rm \in RM: rmState[rm] = "committed") => tmState = "committed"
  /\ tmState = "committed" => /\ tmPrepared = RM
                            /\ \A rm \in RM: rmState[rm] \notin {"working", "aborted"}
                            /\ ([type |-> "Commit"] <: MT) \in msgs
  /\ tmState = "aborted" => ([type |-> "Abort"] <: MT) \in msgs
  /\ \A rm \in RM:
    /\ rm \in tmPrepared =>
      /\ rmState[rm] /= "working"
      /\ ([type |-> "Prepared", rm |-> rm] <: MT) \in msgs
    /\ rmState[rm] = "working" => [type |-> "Prepared", rm |-> rm] \notin msgs
    /\ [type |-> "Prepared", rm |-> rm] \in msgs => rmState[rm] /= "working" 
    /\ rmState[rm] = "aborted" =>
      \/ ([type |-> "Abort"] <: MT) \in msgs
      \/ ([type |-> "Prepared", rm |-> rm] <: MT) \notin msgs
  /\ ([type |-> "Abort"] <: MT) \in msgs =>
    \* it is either the TM or an RM who was in the "working" state
    \/ tmState = "aborted"
    \/ \E rm \in RM:
      /\rmState[rm] = "aborted"
      /\ rm \notin tmPrepared
      /\ ([type |-> "Prepared", rm |-> rm] <: MT) \notin msgs                 
  /\ ([type |-> "Commit"] <: MT) \in msgs =>
    /\ tmPrepared = RM
    /\ \/ tmState = "committed"
       \/ \E rm \in RM: rmState[rm] = "committed"                     
       *)
       
 
TPTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RM
  /\ msgs \in SUBSET Message
  (*/\ tmPrepared \subseteq RM
  /\ msgs \subseteq Message*)

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

(*
 Igor: it took me about a day to find this inductive invariant by refining
 TLC counterexamples. A blind refinement of the counterexamples did not work.
 I had to understand the whole history of every computation that is leading
 to every state.
 *) 
Inv ==
    /\ TPTypeOK
    /\ TCConsistent 
    /\ (\E rm \in RM: rmState[rm] = "committed") => tmState = "committed"
    /\ tmState = "committed" => /\ tmPrepared = RM
                                /\ \A rm \in RM: rmState[rm] \notin {"working", "aborted"}
                                /\ ([type |-> "Commit"] <: MT) \in msgs
    /\ tmState = "aborted" => ([type |-> "Abort"] <: MT) \in msgs
    /\ \A rm \in RM:
      /\ rm \in tmPrepared =>
        /\ rmState[rm] /= "working"
        /\ ([type |-> "Prepared", rm |-> rm] <: MT) \in msgs
      /\ rmState[rm] = "working" => [type |-> "Prepared", rm |-> rm] \notin msgs
      /\ [type |-> "Prepared", rm |-> rm] \in msgs => rmState[rm] /= "working" 
      /\ rmState[rm] = "aborted" =>
        \/ ([type |-> "Abort"] <: MT) \in msgs
        \/ ([type |-> "Prepared", rm |-> rm] <: MT) \notin msgs
    /\ ([type |-> "Abort"] <: MT) \in msgs =>
        \* it is either the TM or an RM who was in the "working" state
        \/ tmState = "aborted"
        \/ \E rm \in RM:
          /\rmState[rm] = "aborted"
          /\ rm \notin tmPrepared
          /\ ([type |-> "Prepared", rm |-> rm] <: MT) \notin msgs                 
    /\ ([type |-> "Commit"] <: MT) \in msgs =>
        /\ tmPrepared = RM
        /\ \/ tmState = "committed"
           \/ \E rm \in RM: rmState[rm] = "committed"                     

(*
THEOREM TPSpec => []TPTypeOK
  (*************************************************************************)
  (* This theorem asserts that the type-correctness predicate TPTypeOK is  *)
  (* an invariant of the specification.                                    *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now assert that the Two-Phase Commit protocol implements the         *)
(* Transaction Commit protocol of module $TCommit$.  The following         *)
(* statement defines $TC!TCSpec$ to be formula $TSpec$ of module           *)
(* $TCommit$.  (The TLA$^+$ \textsc{instance} statement is used to rename  *)
(* the operators defined in module $TCommit$ avoids any name conflicts     *)
(* that might exist with operators in the current module.)                 *)
(***************************************************************************)
TC == INSTANCE TCommit 

THEOREM TPSpec => TC!TCSpec
  (*************************************************************************)
  (* This theorem asserts that the specification TPSpec of the Two-Phase   *)
  (* Commit protocol implements the specification TCSpec of the            *)
  (* Transaction Commit protocol.                                          *)
  (*************************************************************************)
(***************************************************************************)
(* The two theorems in this module have been checked with TLC for six      *)
(* RMs, a configuration with 50816 reachable states, in a little over a    *)
(* minute on a 1 GHz PC.                                                   *)
(***************************************************************************)
*)
=============================================================================
