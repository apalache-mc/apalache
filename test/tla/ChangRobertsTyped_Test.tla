--------------------- MODULE ChangRobertsTyped_Test -------------------------
(*
 * A test setup for ChangRobertsTyped.
 *)
EXTENDS Integers, Apalache

\* a copy of constants from ChangRobertsTyped
CONSTANTS
    \* @type: Int;
    N,
    \* @type: Int -> Int;
    Id

\* a copy of state variables from ChangRobertsTyped
VARIABLES
    \* @type: Int -> Set(Int);
    msgs,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Bool;
    initiator,
    \* @type: Int -> Str;
    state

INSTANCE ChangRobertsTyped

\* We bound N in the test
MAX_N == 6

\* we override Node, as N is not known in advance
OVERRIDE_Node == { i \in 1..MAX_N: i <= N }

\* initialize constants
ConstInit ==
    /\ N \in 2..MAX_N
    /\ Id \in [ 1..MAX_N -> Int ]

\* The below constraints are copied from ASSUME.
\* They are not enforced automatically, see issue #69.
Assumptions ==    
    /\ Node = DOMAIN Id
    /\ \A n \in Node: Id[n] >= 0
    /\ \A m,n \in Node : m # n => Id[m] # Id[n]  \* IDs are unique

InitAndAssumptions ==
    Init /\ Assumptions

(********************** STATELESS OPERATOR TESTS ******************************)

\* Note that succ(n) is not referring to state variables,
\* so we can test it in isolation.
\*
\* @require(ConstInit)
\* @testStateless
Test_succ ==
    \* This is like a property-based test.
    \* Note that it is exhaustive (for the range of N).
    \A n \in Node:
        succ(n) \in Node

\* We could also use a generator, though it is not very useful in case of integers.
\*
\* @testStateless
Test_succ_gen ==
    \* A property-based test with generators.
    \* That looks like the canonical form of PBT.
    \A n \in { Gen(1) }:
       (n \in Node) => succ(n) \in Node

(*************************** ACTION TESTS *************************************)

\* Assertion that we expect to hold true after firing Action_n0.
Assert_n0 ==
    \E n, m \in Node:
        msgs'[n] = msgs[n] \union {m}

\* Execute the action under test.
\* Note that we decouple Assert_n0 from TestAction_n0.
\* The reason is that we always assume that TestAction_n0 always holds,
\* whereas we may want to see Assert_n0 violated.
\*
\* @require(ConstInit)
\* @require(TypeOK)
\* @ensure(Assert_n0)
\* @testAction
TestAction_n0 ==
    \E self \in Node:
        n0(self)

\* Preparing the inputs for the second test. Note that this is a step of its own.
\* This is similar to an initialization predicate.
Prepare_n0 ==
    \* the following constraint should be added automatically in the future
    /\ Assumptions
    \* let the solver pick some data structures within the bounds
    \* up to 15 messages
    /\ msgs = Gen(3 * MAX_N)
    /\ pc = Gen(MAX_N)
    /\ initiator = Gen(MAX_N)
    /\ state = Gen(MAX_N)
    \* restrict the contents with TypeOK,
    \* so we don't generate useless data structures
    /\ TypeOK

\* Another version of the test where we further restrict the inputs.
\* 
\* @require(ConstInit)
\* @require(Prepare_n0)
\* @ensure(Assert_n0)
\* @testAction
TestAction2_n0 ==
    \E self \in Node:
        n0(self)

(*************************** EXECUTION TESTS **********************************)
\* Execute a sequence of 5 actions, similar to TestAction_n0.
\* We test a final state with Assert_n0.
\*
\* @require(ConstInit)
\* @require(TypeOK)
\* @ensure(Assert_noWinner)
\* @testExecution(5)
TestExec_n0_n1 ==
    \* in this test, we only execute actions by processes 1 and 2
    \E self \in { 1, 2 }:
        n0(self) \/ n1(self)

\* We expect no winner.
Assert_noWinner ==
    \A n \in Node:
        state'[n] /= "won"

\* Execute a sequence of 5 actions, while using temporal properties.
\*
\* @require(ConstInit)
\* @require(TypeOK)
\* @require(Liveness)
\* @ensure(GlobalCorrectness)
\* @testExecution(5)
TestExec_correctness_under_liveness ==
    \E self \in Node:
        n0(self) \/ n1(self)

GlobalCorrectness == []Correctness
    
=============================================================================
