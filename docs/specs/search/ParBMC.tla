------------------------------- MODULE ParBMC -------------------------------
(*
 Parallel bounded model checking that extends the sequential search SeqBMC
 by parallelizing enabledness checking and invariant checking.
 For the details on the sequential search, check SeqBMC.tla.
 
 The idea of the parallel search is to have a pool of workers that can switch
 between the two roles:
 
  - 'explorer' are collectively constructing the prefix of the execution space
    by checking with SMT which transitions are provably enabled at every depth.
    When an explorer discovers a new extension of the execution prefix, it deposits
    the prefix as work for a prover. Explorer are using incremental SMT, as they
    have to push and pop contexts often. Explorers are recording their SMT contexts
    and passing a snapshot of the SMT context (with push/pop removed) to the provers.
    Explorers mainly focus on the satisfiable problems, such as whether a transition
    is enabled.
    
  - 'provers' are checking the invariants for the prefixes that were discovered
    by the scouts. Once a prover has checked the invariant and found no violation,
    the prefix is known to be safe. Provers are using non-incremental SMT,
    as every individual piece of work is well-defined. Provers mainly focus on the
    unsatisfiable problems, such as whether the invariant is violated. 
 
 Igor Konnov, 2019
 *)
 
EXTENDS Integers, Sequences 
 
CONSTANT NTRANS,    \* number of symbolic transitions extracted from Next 
         MAX_DEPTH, \* maximal depth to explore
         NWORKERS   \* the number of worker threads

\* Here we model transitions just by numbers.
\* In Apalache, the transitions are TLA+ formulas (which are assigned numbers)
Transitions == 1..NTRANS

\* the worker threads
Workers == 1..NWORKERS

\* Since we are dealing with an abstract model checker, we describe an invariant
\* violation as a set of transition sequences that lead to a bad workerState.
BadExes == { <<0, 1, 2, 1, 2>> }

\* a worker's workerState
WorkerStates ==
    [type: {"idle", "error", "noerror", "deadlock"}]
        \cup
        \* the process is checking, whether a transition tr is feasible
    [type: {"exploring"}, tr: Transitions]
        \cup
        \* the process is checking, whether the invariant holds true for a prefix
    [type: {"proving"}, prefix: Seq(SUBSET Transitions)]

VARIABLES
    (* current exploration depth <= MAX_DEPTH *)
    depth,
    (* the sequence of enabled transitions up to the current depth,
       e.g., { {1, 2}, {1, 2, 3}, {2} } *)  
    runningPrefix,
    (* a set of sequences of enabled transitions that should be checked separately,
       owing to the timeouts *)
    slowPrefixes,       
    (*  { "idle", "exploring", "mining", "error", "noerror", "deadlock" } *)
    workerState,
    (* a function Transitions -> { "new", "borrowed", "enabled", "disabled", "timeout" } *)
    runningTrans,
    (* a set of prefixes, for which the invariants should be checked *)
    unsafePrefixes
    
vars == <<depth, runningPrefix, slowPrefixes, workerState, runningTrans, unsafePrefixes>>    

\* Transform the sequences of sets into a set of sequences.
\* This operator constructs an overapproximation of the execution space.
\* The actual executions in this overapproximation are found by the SMT solver.
RECURSIVE PrefixesToExes(_)    
PrefixesToExes(pref) ==
    IF pref = <<>>
    \* the only execution is the empty one
    THEN {<<>>}
    \* get a transition from the head and concatenate it with all possible extensions
    ELSE { <<tr>> \o suffix: tr \in Head(pref), suffix \in PrefixesToExes(Tail(pref)) }    

\* In the implementation, we give the solver the constraints that stem from the set of prefixes.
\* Here, we model the constraint solving just by checking whether a "bad" execution can be
\* produced by the prefix. 
SMT(pPrefixes) ==
    IF BadExes \intersect PrefixesToExes(pPrefixes) /= {}
    THEN "sat"      \* the SMT solver has found a counterexample
    ELSE "unsat"    \* no counterexample so far

Init ==
    \* The prefixes is initialized with transition 0 that corresponds to Init.
    \* In the implementation, there may be several initializing transitions.
    \* We are using transition 0 for simplicity, and assume that it is enabled.
    /\ runningPrefix = <<{0}>>
    /\ depth = 1
    /\ workerState = [w \in Workers |-> [type |-> "idle"]]
    /\ runningTrans = [t \in Transitions |-> "new"] \* check the transitions for the first step
    /\ unsafePrefixes = {<<{0}>>}    \* check the invariant for the initial workerState
    /\ slowPrefixes = {}    \* there are no slow prefixes yet

\* borrow one transition, in order to check its feasibility later
BorrowTransition(w) ==
    /\ workerState[w].type = "idle"
    /\ \E tr \in Transitions:
        /\ runningTrans[tr] = "new"
        /\ runningTrans' = [runningTrans EXCEPT ![tr] = "borrowed"]
        /\ workerState' = [workerState EXCEPT ![w] = [type |-> "exploring", tr |-> tr]]
    /\ UNCHANGED <<depth, runningPrefix, slowPrefixes, unsafePrefixes>>
        
\* check the borrowed transition for feasibility
CheckOneTransition(w) ==
    /\ workerState[w].type = "exploring"
        \* The SMT solver checks satisfiability of the transition workerState.tr
        \* in the context of the prefixes
    /\ \E outcome \in { "enabled", "disabled", "timeout" }:
          \* the SMT solver checked satisfiabilty and returned: sat, unsat, or timeout
        /\ runningTrans' = [runningTrans EXCEPT ![workerState[w].tr] = outcome]
        /\ workerState' = [workerState EXCEPT ![w] = [type |-> "idle"]]
        /\  IF outcome = "enabled"
            THEN unsafePrefixes' = unsafePrefixes \cup { Append(runningPrefix, {workerState[w].tr}) } 
            ELSE UNCHANGED unsafePrefixes
    /\ UNCHANGED <<depth, runningPrefix, slowPrefixes>>
    
\* go in the proving mode
StartProving(w) ==
    /\ workerState[w].type = "idle"
    /\ \E prefix \in unsafePrefixes:
        /\ workerState' = [workerState EXCEPT ![w] = [type |-> "proving", prefix |-> prefix]]
        /\ unsafePrefixes' = unsafePrefixes \ {prefix}
    /\ UNCHANGED <<depth, runningPrefix, runningTrans, slowPrefixes>>
    
\* try to prove or disprove the invariant for a given prefix    
ProveInvariant(w) ==
    /\ workerState[w].type = "proving"
    /\ LET newState ==  
         IF SMT(workerState[w].prefix) = "sat"
         THEN [type |-> "error"]
         ELSE [type |-> "idle"]
       IN
       workerState' = [workerState EXCEPT ![w] = newState]
    /\ UNCHANGED <<depth, runningPrefix, runningTrans, slowPrefixes, unsafePrefixes>>
    
\* find transitions that timed out and add them to the slow prefixes    
FindSlowPrefixes ==
    LET timedOut == {tr \in Transitions: runningTrans[tr] = "timeout"} IN
        IF timedOut = {}
        THEN slowPrefixes
        ELSE slowPrefixes \cup { Append(runningPrefix, {tr}): tr \in timedOut }

\* all transitions at the current depth have been explored, move on
IncreaseDepth == 
    /\ depth + 1 <= MAX_DEPTH
        \* there is no deadlock
    /\ \E tr \in Transitions: runningTrans[tr] = "enabled"
        \* for every transition at the current depth, we know whether it is enabled or disabled
    /\ \A tr \in Transitions: runningTrans[tr] \in { "enabled", "disabled", "timeout" }
    /\ slowPrefixes' = FindSlowPrefixes \* postpone slow transitions for future checks
    /\ depth' = depth + 1
    /\ runningTrans' = [t \in Transitions |-> "new"]
    /\ UNCHANGED <<unsafePrefixes, workerState>>
        \* extend the prefix with the enabled transitions
    /\  LET enabled == {tr \in Transitions: runningTrans[tr] = "enabled"} IN
            \* continue exploring the fast enabled transitions
        runningPrefix' = Append(runningPrefix, enabled)

\* all transitions at the current depth are either disabled or timed out (or max depth is reached)        
SwitchSlowPrefix ==
    \* all transitions have been explored, so that:
    \* (1) either they are all disabled or timed out,
    \* (2) or the maximum depth has been reached
    /\ LET ToCheck ==
        IF depth < MAX_DEPTH
        THEN { "disabled", "timeout" }
        ELSE { "enabled", "disabled", "timeout" }
       IN
       \A tr \in Transitions: runningTrans[tr] \in ToCheck
    /\ runningTrans' = [t \in Transitions |-> "new"]
    /\ UNCHANGED <<unsafePrefixes, workerState>>
    /\ LET slow == FindSlowPrefixes IN
        /\ slowPrefixes' = slow
        \* pick a slow prefix for exploration, if there is one
        /\ \E oneSlowPrefix \in slow:
            /\ runningPrefix' = oneSlowPrefix
            /\ depth' = Len(oneSlowPrefix) + 1
    
\* No progress is possible. This is not a deadlock, as we split the execution space.
WhenAllDisabledButNotFinished ==
    /\ \A tr \in Transitions: runningTrans[tr] = "disabled"
    /\ runningTrans' = [t \in Transitions |-> "new"]
    /\ UNCHANGED <<slowPrefixes, unsafePrefixes, workerState>>
    /\ \E oneSlowPrefix \in slowPrefixes:
        /\ runningPrefix' = oneSlowPrefix
        /\ depth' = 1 + Len(oneSlowPrefix)
    
\* report no error as there all invariants hold true and the maximum depth has been reached
FinishNoError ==
    /\ unsafePrefixes = {}
    /\ slowPrefixes = {}
    /\ \/ \A tr \in Transitions: runningTrans[tr] = "disabled" 
       \/ /\ depth = MAX_DEPTH
          /\ \A tr \in Transitions: runningTrans[tr] \in { "enabled", "disabled" }
    /\ workerState' = [w \in Workers |-> [type |-> "noerror"]]
    /\ UNCHANGED <<depth, runningPrefix, runningTrans, slowPrefixes, unsafePrefixes>>

\* is the search finished
Finished ==
    /\ \A w \in Workers: workerState[w].type \in { "noerror", "error", "deadlock" }
    /\ UNCHANGED vars

\* The next step of the search
Next ==
    \/ IncreaseDepth
    \/ SwitchSlowPrefix
    \/ WhenAllDisabledButNotFinished
    \/ FinishNoError
    \/ Finished
    \/ \E w \in Workers:
        \/ BorrowTransition(w)
        \/ CheckOneTransition(w)
        \/ StartProving(w)
        \/ ProveInvariant(w)
    
(********************************** PROPERTIES ****************************)
NeverNoError ==
    \A w \in Workers: workerState[w].type /= "noerror"

NeverError ==
    \A w \in Workers: workerState[w].type /= "error"

NeverDeadlock ==
    \A w \in Workers: workerState[w].type /= "deadlock"
    
NeverParallel ==
    \E w \in Workers: workerState[w].type = "idle"    

=============================================================================
\* Modification History
\* Last modified Wed Dec 11 21:39:00 CET 2019 by igor
\* Created Tue Dec 03 12:38:47 CET 2019 by igor
