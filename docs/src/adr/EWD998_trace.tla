------------------------------- MODULE EWD998_traceQuant -------------------------------
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
 token       \* token structure

vars == <<active, color, counter, pending, token>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token \in Token
------------------------------------------------------------------------------
 
Init ==
  (* EWD840 but nodes *) 
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  (* Rule 0 *)
  /\ counter = [i \in Node |-> 0] \* c properly initialized
  /\ pending = [i \in Node |-> 0]
  /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

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

\* @type: (STATE, Int) => Bool;
PassTokenEnabled(state, i) ==
  /\ ~state.active[i] \* If machine i is active, keep the token.
  /\ state.token.pos = i

\* @type: STATE => Bool;
InitiateProbeEnabled(state) ==
  /\ state.token.pos = 0
  /\ \* previous round not conclusive if:
     \/ state.token.color = "black"
     \/ state.color[0] = "black"
     \/ state.counter[0] + state.token.q > 0

\* @type: STATE => Bool;
SystemEnabled(state) ==
  \/ \E i \in Node \ {0}: PassTokenEnabled(state, i)
  \/ InitiateProbeEnabled(state)

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

Next == (System \/ Environment)

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

\* @type: (Seq(STATE), Int) => Bool;
LoopOK(hist, loopIndex) ==
	LET lastState == hist[Len(hist)] IN
  LET loopState == hist[loopIndex] IN
  /\ loopState.active = lastState.active
  /\ loopState.color = lastState.color
  /\ loopState.counter = lastState.counter
  /\ loopState.pending = lastState.pending
  /\ loopState.token = lastState.token

\* @type: Seq(STATE) => Bool;
IsLoopOK(hist) ==
  \E loopIndex \in DOMAIN hist:
    LoopOK(hist, loopIndex)

\* @type: (Seq(STATE), Int) => Bool;
LoopFair(hist, loopIndex) ==
  \A index \in {x \in DOMAIN hist: x >= loopIndex}:
    ~SystemEnabled(hist[index])

\* @type: STATE => Bool;
TerminationIn(state) == 
  /\ \A i \in Node : ~ state.active[i]
  /\ FoldFunction(Plus, 0, state.pending) = 0

\* @type: STATE => Bool;
terminationDetectedIn(state) ==
  /\ state.token.pos = 0
  /\ state.token.color = "white"
  /\ state.token.q + state.counter[0] = 0
  /\ state.color[0] = "white"
  /\ ~ state.active[0]
  /\ state.pending[0] = 0

\* @type: (Seq(STATE), Int) => Bool;
Live(hist, loopIndex) ==
  \A firstIndex \in DOMAIN hist:
    (TerminationIn(hist[firstIndex]) =>
      LET lowerBound == IF firstIndex > loopIndex THEN loopIndex ELSE firstIndex IN
      \E secondIndex \in {x \in DOMAIN hist: x >= lowerBound}:
        terminationDetectedIn(hist[secondIndex]))

\* @type: Seq(STATE) => Bool;
Property(hist) ==
  \A loopIndex \in DOMAIN hist:
    LoopOK(hist, loopIndex) /\ LoopFair(hist, loopIndex) =>
        Live(hist, loopIndex)

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