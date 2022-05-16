-------------------------- MODULE BasicChecker --------------------------------
(*
 * A basic specification of the exploration algorithm that is implemented in
 * Apalache. We focus on the algorithm itself and omit the non-essential parts.
 * Hence, we make the following assumptions:
 *
 * - The set of states and the transition relation are predefined.
 * 
 * - For simplicity, we consider all states to be encoded with integers,
 * instead of considering complex data structures.
 *
 * Igor Konnov, Informal Systems, 2022
 *)

EXTENDS Integers, Sequences, Apalache, Solver_typedefs

CONSTANTS
    \* The set of all potential states.
    \*
    \* @type: Set(Int);
    STATES,
    \* The set of the initial states.
    \*
    \* @type: Set(Int);
    INIT_STATES,
    \* The set of all potential transitions.
    \*
    \* @type: Set(<<Int, Int>>);
    TRANSITIONS,
    \* The invariant to be checked.
    \*
    \* @type: Set(Int);
    INVARIANT,
    \* The maximal number of steps to consider.
    \*
    \* @type: Int;
    MAX_STEPS

VARIABLES
    \* The state of the search.
    \*
    \* @type: { code: Str, trace: Seq(Int) };
    searchState,
    \* The current step.
    \*
    \* @type: Int;
    stepNo,
    \* The solver state
    \*
    \* @type: CONTEXT;
    context

INSTANCE Solver    

TIME_FRAMES == 1..MAX_STEPS + 1

CheckStep(ctx, trace) ==
    IF ~IsModel(ctx, trace)
    THEN [ code |-> "Deadlock", trace |-> <<>> ]
    ELSE LET withNotInv == InsertPred(ctx, STATES \ INVARIANT) IN
         IF IsModel(withNotInv, trace)
         THEN [ code |-> "Error", trace |-> trace ]
         ELSE [ code |-> "NoError", trace |-> <<>> ]

Init ==
    /\ stepNo = 0
    /\ context = ContextPush(ContextEmpty, { INIT_STATES }, {})
    /\ \E trace \in [ { 1 } -> STATES ]:
        LET traceSeq == FunAsSeq(trace, 1, 1) IN
        searchState = CheckStep(context, traceSeq)

Next ==
    /\ searchState.code = "NoError"
    /\ stepNo < MAX_STEPS
    /\ stepNo' = stepNo + 1
    /\ \E trace \in [ TIME_FRAMES -> STATES ]:
        LET traceSeq == FunAsSeq(trace, stepNo + 2, MAX_STEPS + 1) IN
        LET newCtx == ContextPush(context, {}, { TRANSITIONS }) IN
        /\ context' = newCtx
        /\ searchState' = CheckStep(newCtx, traceSeq)

\* Check this invariant to see, whether there is a counterexample
NoError ==
    searchState.code /= "Error"

\* @type: Seq(Int) => Bool;
IsExecution(trace) ==
    /\ 1 \in DOMAIN trace
    /\ trace[1] \in INIT_STATES
    /\ \A i \in DOMAIN trace \ { 1 }:
        <<trace[i - 1], trace[i]>> \in TRANSITIONS

Soundness ==
    LET trace == searchState.trace IN
    searchState.code = "Error"
        =>  /\ IsExecution(trace)
            /\ trace[Len(trace)] \notin INVARIANT

Completeness ==
    \E n \in 1..MAX_STEPS + 1:
        LET ExistsExecution ==
            /\ \E trace \in [ TIME_FRAMES -> STATES ]:
                LET traceSeq == FunAsSeq(trace, n, MAX_STEPS + 1) IN
                /\ IsExecution(traceSeq)
                /\ traceSeq[Len(traceSeq)] \notin INVARIANT
            /\ stepNo >= n - 1
        IN
        ExistsExecution => searchState.code = "Error"

=============================================================================== 

