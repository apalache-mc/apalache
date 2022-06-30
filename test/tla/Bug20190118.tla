------------------------------- MODULE Bug20190118 ------------------------ 
\* this is a minimal working example that caused a bug
\* it stems from TwoPhase.tla
EXTENDS Variants

(*
 @typeAlias: MESSAGE = Commit(NIL) | Abort(NIL) | Prepared(RM);
 *)
TwoPhaseTyped_aliases == TRUE

\* @type: MESSAGE;
MkCommit == Variant("Commit", "0_OF_NIL")

\* @type: MESSAGE;
MkAbort == Variant("Abort", "0_OF_NIL")

\* @type: RM => MESSAGE;
MkPrepared(rm) == Variant("Prepared", rm)

RM == { "1_OF_RM", "2_OF_RM"}

VARIABLES
  \* @type: RM -> Str;
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  \* @type: Set(RM);
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
  \* @type: Set(MESSAGE);
  msgs

\* @type: Set(MESSAGE);
Message ==
  { MkPrepared(rm): rm \in RM }
    \union
  { MkAbort, MkCommit }

Init ==  
  /\ rmState \in [RM -> {"working", "prepared"}]
  /\ msgs \in SUBSET Message \* this is a problematic statement
  /\ rmState["1_OF_RM"] = "working"
  /\ rmState["2_OF_RM"] = "prepared"
  /\ tmPrepared = {"2_OF_RM"}
  /\ msgs = { MkPrepared("2_OF_RM") }

TMCommit ==
  /\ tmPrepared = RM
  /\ msgs' = msgs \union { MkCommit }
  /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \union { MkPrepared(rm) }
  /\ UNCHANGED tmPrepared

Next == TMCommit \/ RMPrepare("1_OF_RM")
-----------------------------------------------------------------------------
\* this invariant cannot be violated in one step
Inv == MkCommit \notin msgs

=============================================================================
