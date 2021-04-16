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

\* Preparing the inputs for the test. Note that this is a step of its own.
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

\* Assertion that we expect to hold true after firing Action_n0.
Assert_n0 ==
    \E n, m \in Node:
        msgs'[n] = msgs[n] \union {m}

\* Execute the action under test.
\* Note that we decouple Assert_n0 from TestAction_n0.
\* The reason is that we always assume that TestAction_n0 always holds,
\* whereas we may want to see Assert_n0 violated.
\*
\* @require("Prepare_n0")
\* @ensure("Assert_n0")
\* @testAction
TestAction_n0 ==
    \E self \in Node:
        n0(self)
    
=============================================================================
