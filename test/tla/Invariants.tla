---------------------------- MODULE Invariants --------------------------------
EXTENDS Integers, Sequences, FiniteSets

VARIABLES
    \* @typeAlias: S = Set(Int);
    \* @typeAlias: STATE = [ In: S, Done: S, Out: S ];
    \* @type: S;
    In,
    \* @type: S;
    Done,
    \* @type: S;
    Out

\* @type: <<S, S, S>>;
vars == <<In, Done, Out>>

Init ==
    /\ \E S \in SUBSET (1..5):
        /\ Cardinality(S) > 2
        /\ In = S
    /\ Done = {}
    /\ Out = {}

Next ==
    \/ \E x \in In:
        /\ In' = In \ { x }
        /\ Done' = Done \union { x }
        /\ Out' = Out \union { 2 * x }
    \/ In = {} /\ UNCHANGED vars

\* state invariants that reason about individual states

StateInv ==
    Done \intersect In = {}

BuggyStateInv ==
    Done \subseteq In

\* action invariants that reason about transitions (pairs of states)

ActionInv ==
    \/ In = {}
    \/ \E x \in Done':
        Done' = Done \union { x }

BuggyActionInv ==
    Cardinality(In') = Cardinality(In) + 1

\* trace invariants that reason about executions

\* @type: Seq(STATE) => Bool;
TraceInv(hist) ==
    \/ hist[Len(hist)].In /= {}
    \* note that we are using the last state in the history and the first one
    \/ { 2 * x: x \in hist[1].In } = hist[Len(hist)].Out

\* @type: Seq(STATE) => Bool;
BuggyTraceInv(hist) ==
    \/ hist[Len(hist)].In /= {}
    \* note that we are using the last state in the history and the first one
    \/ { 3 * x: x \in hist[1].In } = hist[Len(hist)].Out

===============================================================================
