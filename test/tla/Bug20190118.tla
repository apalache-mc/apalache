------------------------------- MODULE Bug20190118 ------------------------ 
\* this is a minimal working example that caused a bug
\* it stems from TwoPhase.tla

(* BMCMT extensions *)
RM == {"r1", "r2"}

\* new: a message type
MT == [type |-> STRING, rm |-> STRING]
(* END OF BMCMT extensions *)

VARIABLES
  \* @type: Str -> Str;
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  \* @type: Set(Str);
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
  \* @type: Set([type: Str, rm: Str]);
  msgs

Message ==
  {[type |-> t, rm |-> r]: t \in {"Prepared"}, r \in RM }
    \union
  {[type |-> t] : t \in {"Commit", "Abort"} }

Init ==  
  /\ rmState \in [RM -> {"working", "prepared"}]
  /\ msgs \in SUBSET Message \* this is a problematic statement
  /\ rmState["r1"] = "working"
  /\ rmState["r2"] = "prepared"
  /\ tmPrepared = {"r2"}
  /\ msgs = {[type |-> "Prepared", rm |-> "r2"]}

TMCommit ==
  /\ tmPrepared = RM
  /\ msgs' = msgs \union {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED tmPrepared

Next == TMCommit \/ RMPrepare("r1")
-----------------------------------------------------------------------------
\* this invariant cannot be violated in one step
Inv == [type |-> "Commit"] \notin msgs

=============================================================================
