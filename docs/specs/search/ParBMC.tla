------------------------------- MODULE ParBMC -------------------------------
(*
 Parallel bounded model checking that extends the sequential search SeqBMC
 by parallelizing enabledness checking and invariant checking.
 For the details on the sequential search, check SeqBMC.tla.
 
 The idea of the parallel search is to have a pool of workers that can switch
 between the two roles:
 
  - 'scouts' are collectively constructing the prefix of the execution space
    by checking with SMT which transitions are provably enabled at every depth.
    When a scout discovers a new extension of the execution prefix, it deposits
    the prefix as work for a miner. Scouts are using incremental SMT, as they
    have to push and pop contexts often. Scouts are recording their SMT contexts
    and passing a snapshot of the SMT context (with push/pop removed) to the miners.
    Scouts mainly focus on the satisfiable problems, such as whether a transition
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
    [type: {"scouting"}, tr: Transitions]
        \cup
        \* the process is checking, whether the invariant holds true for a prefix
    [type: {"proving"}, prefix: Seq(SUBSET Transitions)]

VARIABLES
    prefixes,       \* the sequence of enabled transitions up to the current depth,
                    \* e.g., { {1, 2}, {1, 2, 3}, {2} }
    depth,          \* current exploration depth <= MAX_DEPTH
    workerState,    \* \in { "idle", "scouting", "mining", "error", "noerror", "deadlock" }
    openTrans,      \* a function Transitions -> { "new", "borrowed", "enabled", "disabled" }
    unsafePrefixes  \* a set of prefixes, for which the invariants should be checked
    
vars == <<prefixes, depth, workerState, openTrans, unsafePrefixes>>    

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
    /\ prefixes = <<{0}>>
    /\ depth = 1
    /\ workerState = [w \in Workers |-> [type |-> "idle"]]
    /\ openTrans = [t \in Transitions |-> "new"] \* check the transitions for the first step
    /\ unsafePrefixes = {<<{0}>>}    \* check the invariant for the initial workerState

\* borrow one transition, in order to check its feasibility later
BorrowTransition(w) ==
    /\ workerState[w].type = "idle"
    /\ \E tr \in Transitions:
        /\ openTrans[tr] = "new"
        /\ openTrans' = [openTrans EXCEPT ![tr] = "borrowed"]
        /\ workerState' = [workerState EXCEPT ![w] = [type |-> "scouting", tr |-> tr]]
    /\ UNCHANGED <<prefixes, depth, unsafePrefixes>>
        
\* check the borrowed transition for feasibility
CheckOneTransition(w) ==
    /\ workerState[w].type = "scouting"
        \* The SMT solver checks satisfiability of the transition workerState.tr
        \* in the context of the prefixes
    /\ \E is_sat \in BOOLEAN:   \* the SMT solver has checked satisfiability
        LET outcome == IF is_sat THEN "enabled" ELSE "disabled" IN
        /\ openTrans' = [openTrans EXCEPT ![workerState[w].tr] = outcome]
        /\ workerState' = [workerState EXCEPT ![w] = [type |-> "idle"]]
        /\  IF is_sat
            THEN unsafePrefixes' = unsafePrefixes \cup { Append(prefixes, {workerState[w].tr}) } 
            ELSE UNCHANGED unsafePrefixes
    /\ UNCHANGED <<prefixes, depth>>
    
\* go in the proving mode
StartProving(w) ==
    /\ workerState[w].type = "idle"
    /\ \E prefix \in unsafePrefixes:
        /\ workerState' = [workerState EXCEPT ![w] = [type |-> "proving", prefix |-> prefix]]
        /\ unsafePrefixes' = unsafePrefixes \ {prefix}
    /\ UNCHANGED <<prefixes, depth, openTrans>>
    
\* try to prove or disprove the invariant for a given prefix    
ProveInvariant(w) ==
    /\ workerState[w].type = "proving"
    /\ LET newState ==  
         IF SMT(workerState[w].prefix) = "sat"
         THEN [type |-> "error"]
         ELSE [type |-> "idle"]
       IN
       workerState' = [workerState EXCEPT ![w] = newState]
    /\ UNCHANGED <<prefixes, depth, openTrans, unsafePrefixes>>
        
\* all transitions at the current depth have been explored, move on
IncreaseDepth ==
    /\ depth + 1 <= MAX_DEPTH
        \* there is no deadlock
    /\ \E tr \in Transitions: openTrans[tr] = "enabled"
        \* for every transition at the current depth, we know whether it is enabled or disabled
    /\ \A tr \in Transitions: openTrans[tr] \in { "enabled", "disabled" }
    /\ depth' = depth + 1
        \* extend the prefix with the enabled transitions
    /\ prefixes' = Append(prefixes, {tr \in Transitions: openTrans[tr] = "enabled"})
        \* schedule the transition to be checked
    /\ openTrans' = [t \in Transitions |-> "new"]
    /\ UNCHANGED <<unsafePrefixes, workerState>>
    
\* no progress is possible as there is a deadlock
ReportDeadlock(w) ==
    /\ workerState[w].type = "idle"
    /\ \A tr \in Transitions: openTrans[tr] = "disabled"
    /\ workerState' = [workerState EXCEPT ![w] = [type |-> "deadlock"]]
    /\ UNCHANGED <<prefixes, depth, unsafePrefixes, openTrans>>
    
\* report no error as there all invariants hold true and the maximum depth has been reached
ReportNoError(w) ==
    /\ workerState[w].type = "idle"
    /\ depth = MAX_DEPTH
    /\ unsafePrefixes = {} 
    /\ \A tr \in Transitions: openTrans[tr] \in { "enabled", "disabled" }
    /\ workerState' = [workerState EXCEPT ![w] = [type |-> "noerror"]]
    /\ UNCHANGED <<prefixes, depth, unsafePrefixes, openTrans>>

\* is the search finished
Finished ==
    /\ \A w \in Workers: workerState[w].type \in { "noerror", "error", "deadlock" }
    /\ UNCHANGED vars

\* The next step of the search
Next ==
    \/ IncreaseDepth
    \/ Finished
    \/ \E w \in Workers:
        \/ BorrowTransition(w)
        \/ CheckOneTransition(w)
        \/ StartProving(w)
        \/ ProveInvariant(w)
        \/ ReportDeadlock(w)
        \/ ReportNoError(w)
    
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
\* Last modified Wed Dec 11 17:49:07 CET 2019 by igor
\* Created Tue Dec 03 12:38:47 CET 2019 by igor
