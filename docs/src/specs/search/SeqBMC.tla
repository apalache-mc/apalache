------------------------------- MODULE SeqBMC -------------------------------
(*
 Sequential bounded model checking that is implemented in Apalache 0.5.x.
 
 The model checker assumes that Next is partitioned in N transitions, that is,
 Next == Next_1 \/ ... \/ Next_N.
 
 (Apalache also partitions Init, but we assume that it is just one transition here.)
 
 The goal of the model checker is to analyze all the executions whose length does not
 exceed the bound MAX_DEPTH. Similar to breadth first search, Apalache encodes
 possible transitions at every depth k. Importantly, it preprocesses those transitions
 that are provably disabled at depth k. The transitions are uploaded into SMT,
 so the solver is trying to find an execution that violates an invariant.
 The solver does it by solving constraints over Booleans, integers,
 and uninterpreted constants.
 
 If we have exactly two transitions, the classical breadth-first search (as in TLC)
 would analyze executions by layers as follows (notation [i] denotes the ith transition):
 
       *
       |
      [0]
       |
       *
      / \
    [1] [2]
    /     \
   *       *
  / \     / \
 [1][2]  [1][2]
  |  |    |  |
  *  *    *  *
  
 Note that every '*' is a concrete state in the figure. Some states are pruned, as TLC
 find that it has explored these states before.
 
 The search in the symbolic model checker looks like follows:
 
     Phi0
     ----- init -----
     check(Init0) => sat
     assert(Init0)
     check(~Inv) => unsat
     ---- step 1 ----
     check(Next0) => sat
     check(Next0 /\ ~Inv') => unsat
     check(Next1) => sat
     check(Next1 /\ ~Inv') => no 
     assert(Next0 \/ Next1)
     ---- step 2 ----
     check(Next0) => unsat
     check(Next1) => sat
     check(Next1 /\ ~Inv') => unsat
     assert(Next1)
     ---- step 3 ----
     check(Next0) => sat
     check(Next0 /\ ~Inv') => sat => counterexample
       
 The symbolic model checker is adding more and more constraints in the context. It also
 prunes the unsatisfiable constraints during the search (where the solver reported unsat),
 which corresponds to pruning sets of transitions that are provably disabled at given depth. 
 
 
 Igor Konnov, 2019
 *)
 
EXTENDS Integers, Sequences 
 
CONSTANT NTRANS,    \* number of symbolic transitions extracted from Next 
         MAX_DEPTH  \* maximal depth to explore

\* Here we model transitions just by numbers.
\* In Apalache, the transitions are TLA+ formulas.
Transitions == 1..NTRANS

\* Since we are dealing with an abstract model checker, we describe an invariant
\* violation as a set of transition sequences that lead to a bad state.
BadExes == { <<0, 1, 3, 2, 3, 3>> }

VARIABLES
    prefixes,   \* the sequence of enabled transitions up to the currentdepth,
                \* e.g., { {1, 2}, {1, 2, 3}, {2} }
    depth,      \* current exploration depth <= MAX_DEPTH
    state       \* \in { "working", "error", "noerror", "deadlock" } 
    
vars == <<prefixes, depth, state>>    

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

\* Check the invariant for every enabled transition    
IsInvariantViolated(pPrefixes, pEnabled) ==    
    \E tr \in pEnabled:
        SMT(Append(pPrefixes, {tr})) = "sat"

Init ==
    \* The prefixes is initialized with transition 0 that corresponds to Init.
    \* In the implementation, there may be several initializing transitions.
    \* We are using transition 0 for simplicity.
    /\ prefixes = <<{0}>>
    /\ depth = 1
    /\ state =
        IF IsInvariantViolated(<<>>, {0})
        THEN "error"    \* an initial state is violating the invariant
        ELSE "working"  \* the initial states are fine, start the search

\* The next step of the search
NextStep ==
    /\ state = "working"
    \* The implementation tests every transition for satisfiability with SMT.
    \* Efficiently, it is checking, whether a new transition can extend some execution
    \* that is encoded by the sets of transitions in the prefixes.
    \* To model this, we pick an arbitrary subset of transitions. 
    /\ \E enabled \in SUBSET Transitions:
        IF enabled /= {}
        THEN
            IF IsInvariantViolated(prefixes, enabled)
            THEN \* report the counterexample (comes from SMT) and stop
                /\ prefixes' = Append(prefixes, enabled)
                /\ state' = "error"
                /\ UNCHANGED depth
            ELSE \* go one step further
                /\ prefixes' = Append(prefixes, enabled)
                /\ depth' = depth + 1
                /\ state' = IF (depth' >= MAX_DEPTH) THEN "noerror" ELSE state
        ELSE
            /\ UNCHANGED <<prefixes, depth>>
            /\ state' = "deadlock"  

\* is the search finished
Finished ==
    state /= "working" /\ UNCHANGED vars

\* the search is either continuing, or has finished    
Next == NextStep \/ Finished
    
(********************************** PROPERTIES ****************************)
NeverError == state /= "error"    

NeverDeadlock == state /= "deadlock"    

=============================================================================
\* Modification History
\* Last modified Tue Dec 03 16:31:25 CET 2019 by igor
\* Created Tue Dec 03 12:38:47 CET 2019 by igor
