------------------------------- MODULE EWD998_buchiFast -------------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Shmuel Safra, published as EWD 998:         *)
(* Shmuel Safra's version of termination detection.                        *)
(* https://www.cs.utexas.edu/users/EWD/ewd09xx/EWD998.PDF                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Utils, Apalache


N == 5
Node == 0 .. N-1
Color == {"white", "black"}
Token == [pos : Node, q : Int, color : Color]

VARIABLES 
  \* @typeAlias: STATE = [ active: Int -> Bool, color: Int -> Str, counter: Int -> Int, pending:  Int -> Int, token: [pos: Int, q: Int, color: Str]];
  \* @type: Int -> Bool;
  active,     \* activation status of nodes
  \* @type: Int -> Str;
  color,      \* color of nodes
  \* @type: Int -> Int;
  counter,    \* nb of sent messages - nb of rcvd messages per node
  \* @type: Int -> Int;
  pending,    \* nb of messages in transit to node
  \* @type: [pos: Int, q: Int, color: Str];
  token,       \* token structure
  \* @type: Bool;
  InLoop,

  (* loop variables *)
  \* @type: Int -> Bool;
  loop_active,     \* activation status of nodes
  \* @type: Int -> Str;
  loop_color,      \* color of nodes
  \* @type: Int -> Int;
  loop_counter,    \* nb of sent messages - nb of rcvd messages per node
  \* @type: Int -> Int;
  loop_pending,    \* nb of messages in transit to node
  \* @type: [pos: Int, q: Int, color: Str];
  loop_token,       \* token structure

  \* @type: Bool;
  loop_fair,

  \* @type: Int;
  buchi_state,

  \* @type: Int;
  loop_buchi_state,

  \* @type: Bool;
  buchi_acceptingSeen,

  \* @type: Bool;
  PrevInLoop



vars == <<active, color, counter, pending, token>>
loop_vars == <<loop_active, loop_color, loop_counter, loop_pending, loop_token>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token \in Token

\* @type: Int => Bool;
PassTokenEnabled(i) ==
  /\ ~active[i] \* If machine i is active, keep the token.
  /\ token.pos = i

\* @type: Bool;
InitiateProbeEnabled ==
  /\ token.pos = 0
  /\ \* previous round not conclusive if:
     \/ token.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + token.q > 0

\* @type: Bool;
SystemEnabled ==
  \/ \E i \in Node \ {0}: PassTokenEnabled(i)
  \/ InitiateProbeEnabled

------------------------------------------------------------------------------
BuchiInit ==
  buchi_state := 0

AuxInit ==
  /\ InLoop \in {TRUE, FALSE}
  /\ PrevInLoop = FALSE
  /\ loop_vars = vars
  /\ loop_fair = (~InLoop \/ ~SystemEnabled)
  /\ BuchiInit
  /\ loop_buchi_state = buchi_state
  /\ buchi_acceptingSeen := (InLoop /\ buchi_state = 1)

Init ==
  (* EWD840 but nodes *) 
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  (* Rule 0 *)
  /\ counter = [i \in Node |-> 0] \* c properly initialized
  /\ pending = [i \in Node |-> 0]
  /\ token = [pos |-> 0, q |-> 0, color |-> "black"]
  /\ AuxInit

InitiateProbe ==
  (* Rules 1 + 5 + 6 *)
  /\ token.pos = 0
  /\ \* previous round not conclusive if:
     \/ token.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + token.q > 0
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [ color EXCEPT ![0] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter, pending>>                   
  
PassToken(i) ==
  (* Rules 2 + 4 + 7 *)
  /\ ~ active[i] \* If machine i is active, keep the token.
  /\ token.pos = i
  /\ token' = [token EXCEPT !.pos = @ - 1,
                            !.q = @ + counter[i],
                            !.color = IF color[i] = "black" THEN "black" ELSE @]
  /\ color' = [ color EXCEPT ![i] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter, pending>>

System == \/ InitiateProbe
          \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[i]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Node \ {i} : pending' = [pending EXCEPT ![j] = @ + 1]
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color, token>>

RecvMsg(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![i] = "black" ]
  \* Receipt of a message activates i.
  /\ active' = [ active EXCEPT ![i] = TRUE ]
  /\ UNCHANGED <<token>>                           

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pending, token>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Plus(a, b) == a + b

-----------------------------------------------------------------------------

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 and there are *)
(* no in-flight messages then every node is inactive.                      *)
(***************************************************************************)
terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]
  /\ pending[0] = 0

(***************************************************************************)
(* The number of messages on their way. "in-flight"                        *)
(***************************************************************************)
B == FoldFunction(Plus, 0, pending)

(***************************************************************************)
(* The system has terminated if no node is active and there are no         *)
(* in-flight messages.                                                     *)
(***************************************************************************)
Termination == 
  /\ \A i \in Node : ~ active[i]
  /\ B = 0

TerminationDetection ==
  terminationDetected => Termination

(**************************************************************************)

LoopNext ==
  /\ InLoop' \in {TRUE, FALSE}
  /\ loop_active' \in {loop_active, active'}
  /\ loop_color' \in {loop_color, color'}
  /\ loop_counter' \in {loop_counter, counter'}
  /\ loop_pending' \in {loop_pending, pending'}
  /\ loop_token' \in {loop_token, token'}
  /\ loop_buchi_state' \in {loop_buchi_state, buchi_state'}
  /\ (~InLoop /\ InLoop') => (loop_vars' = vars' /\ loop_buchi_state' = buchi_state')
  /\ (InLoop = InLoop') => (loop_vars' = loop_vars /\ loop_buchi_state' = loop_buchi_state)
  /\ (InLoop) => (InLoop')
  /\ PrevInLoop' = InLoop

BuchiNext ==
  /\ buchi_state' \in {0,1,-1}
  /\ (buchi_state' = 1) =>  \/ (buchi_state = 0 /\ Termination /\ ~terminationDetected)
                            \/ (buchi_state = 1 /\ ~terminationDetected)
  /\ (buchi_state' = 0) => (buchi_state = 0)

AuxNext ==
  /\ loop_fair' := (loop_fair /\ (~InLoop' \/ ~SystemEnabled'))
  /\ buchi_acceptingSeen' := 
      \/ buchi_acceptingSeen 
      \/  /\ InLoop'
          /\ buchi_state' = 1

Next == /\ BuchiNext 
        /\ (((System \/ Environment) /\ LoopNext) \/ (UNCHANGED << vars, loop_vars, InLoop, loop_buchi_state >> /\ PrevInLoop' = InLoop)) 
        /\ AuxNext

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* Bound the otherwise infinite state space that TLC has to check.         *)
(***************************************************************************)
StateConstraint ==
  /\ \A i \in Node : counter[i] <= 3 /\ pending[i] <= 3
  /\ token.q <= 9

-----------------------------------------------------------------------------

(***************************************************************************)
(* Safra's inductive invariant                                             *)
(***************************************************************************)

Inv == 
  /\ P0:: B = FoldFunction(Plus, 0, counter)
     (* (Ai: t < i < N: machine nr.i is passive) /\ *)
     (* (Si: t < i < N: ci.i) = q *)
  /\ \/ P1:: /\ \A i \in {x \in Node: (token.pos+1) <= x}: ~ active[i] \* machine nr.i is passive
             /\ IF token.pos = N-1 
                THEN token.q = 0 
                ELSE token.q = FoldFunctionOnSet(Plus, 0, counter, {x \in Node: (token.pos+1) <= x})
     (* (Si: 0 <= i <= t: c.i) + q > 0. *)
     \/ P2:: FoldFunctionOnSet(Plus, 0, counter, {x \in Node: x <= token.pos}) + token.q > 0
     (* Ei: 0 <= i <= t : machine nr.i is black. *)
     \/ P3:: \E i \in {x \in Node: x <= token.pos} : color[i] = "black"
     (* The token is black. *)
     \/ P4:: token.color = "black"

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)

\* @type: Bool;
LoopOK ==
  /\ InLoop /\ PrevInLoop
  /\ loop_active = active
  /\ loop_color = color
  /\ loop_counter = counter
  /\ loop_pending = pending
  /\ loop_token = token
  /\ loop_buchi_state = buchi_state

LoopFair ==
  loop_fair

Property ==
  LoopOK /\ LoopFair => ~buchi_acceptingSeen

Liveness ==
  [](Termination => <>terminationDetected)

(***************************************************************************)
(* The algorithm implements the specification of termination detection     *)
(* in a ring with asynchronous communication.                              *)
(* The parameters of module AsyncTerminationDetection are instantiated     *)
(* by the symbols of the same name of the present module.                  *)
(***************************************************************************)
TD == INSTANCE AsyncTerminationDetection

THEOREM Spec => TD!Spec
=============================================================================

Checked with TLC in 01/2021 with two cores on a fairly modern desktop
and the given state constraint StateConstraint above:

| N | Diameter | Distinct States | States | Time |
| --- | --- | --- | --- | --- |
| 3 | 60 | 1.3m | 10.1m | 42 s |
| 4 | 105 | 219m | 2.3b | 50 m |