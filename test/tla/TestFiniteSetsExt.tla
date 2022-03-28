-------------------- MODULE TestFiniteSetsExt ----------------------------
(*
 * Functional tests for operators over finite sets in the community modules.
 * We introduce a trivial state machine and write tests as state invariants.
 *
 * These tests are derived from:
 *
 * https://github.com/tlaplus/CommunityModules/blob/master/tests/FiniteSetsExtTests.tla
 *)
EXTENDS Integers, FiniteSets, FiniteSetsExt

Init == TRUE
Next == TRUE

\* @type: Set(Int);
EmptySet == {}

(* TESTS *)
TestQuantify1 ==
    LET S == {"a","b","c","c"} IN
    Quantify(S, LAMBDA s: s = "c") = Cardinality({s \in S : s = "c"})

TestQuantify2 ==
    \A S \in SUBSET {"a","b","c","c"} :
          Quantify(S, LAMBDA s: s = "c") = Cardinality({s \in S : s = "c"})

TestQuantify3 ==
    \A S \in SUBSET {"a","b","c","c"} :
          Quantify(S, LAMBDA s: FALSE) = Cardinality({s \in S : FALSE})

TestQuantify4 ==
    LET S == 1..10 IN
    Quantify(S, LAMBDA s: s = 3) = Cardinality({s \in S : s = 3})

TestQuantify5 ==
    LET S == 1..20 IN
    Quantify(S, LAMBDA s: TRUE) = Cardinality(S)    

TestKSubset1 ==
    LET S == {"a","b","c","c"} \* Make sure value normalization works.
    IN
    \A k \in -1..Cardinality(S) + 1: 
        kSubset(k, S) = {s \in SUBSET S : Cardinality(s) = k}

TestKSubset2 ==
    LET S == {"a","b","c","c"} \* Make sure value normalization works.
    IN
    kSubset(-1, S) = {} /\ kSubset(4, S) = {}    

TestKSubset3 ==
    LET S == 1..3 IN
    kSubset(Cardinality(S), S) = { S }

TestKSubset4 ==
    {} \notin kSubset(1, {1, 2, 3})    

TestKSubset5 ==
    LET T == 1..3 IN 
        \A k \in (1..Cardinality(T)):
            /\ \A e \in { ss \in (SUBSET T) : Cardinality(ss) = k}:
                 e \in kSubset(k, T)
            /\ \A e \in { ss \in (SUBSET T) : Cardinality(ss) # k}:
                 e \notin kSubset(k, T)
                     
TestKSubset6 ==
    LET T == {"a","b","c"}
        kSubsetPure(k, S) == { s \in SUBSET S : Cardinality(s) = k }
    IN
    \A k \in 1..Cardinality(T):
        /\ kSubset(k, T) = kSubsetPure(k, T)
        /\ kSubsetPure(k, T) = kSubset(k, T)    

TestKSubset7 ==
    LET T == {"a","b","c"} IN
    /\ kSubset(1, T) = {{"a"},{"b"},{"c"}}
    /\ kSubset(2, T) = {{"a","b"}, {"a","c"}, {"b","c"}}
    /\ kSubset(3, T) = {{"a","b","c"}}
    /\ {{"a"},{"b"},{"c"}} = kSubset(1, T)
    /\ {{"a","b"}, {"a","c"}, {"b","c"}} = kSubset(2, T)
    /\ {{"a","b","c"}} = kSubset(3, T)        

TestKSubset8 ==
    LET T == {"a","b","c"}
        kSubsetPure(k, S) == { s \in SUBSET S : Cardinality(s) = k }
    IN
    /\ { kSubset(k, T) : k \in 2..3 } = { kSubsetPure(k, T) : k \in 2..3 }
    /\ { kSubsetPure(k, T) : k \in 2..3 } = { kSubset(k, T) : k \in 2..3 }
    /\ { kSubsetPure(k, T) : k \in 2..3 } = { kSubset(k, T) : k \in {3,2} }
    /\ (kSubset(2, T) \union kSubset(3, T)) =
            (kSubsetPure(2, T) \union kSubsetPure(3, T))
    /\ (kSubset(3, T) \union kSubset(2, T)) =
            (kSubsetPure(2, T) \union kSubsetPure(3, T))
    /\ (kSubset(1, T) \union kSubset(2, T) \union kSubset(3, T)) =
            (kSubsetPure(2, T) \union kSubsetPure(3, T) \union kSubsetPure(1, T))
    /\ (kSubset(3, T) \union kSubset(1, T) \union kSubset(2, T)) =
            (kSubsetPure(1, T) \union kSubsetPure(2, T)
                \union kSubsetPure(3, T) \union kSubsetPure(3, T))
    /\ (kSubset(3, T) \union kSubset(1, T) \union kSubset(2, T)
        \union kSubset(2, T)) = (kSubsetPure(1, T)
        \union kSubsetPure(2, T) \union kSubsetPure(3, T)
        \union kSubsetPure(3, T))
    /\ (kSubset(3, T) \union kSubset(1, T) \union kSubset(2, T)
        \union kSubset(0, T)) = (kSubsetPure(1, T)
        \union kSubsetPure(2, T) \union kSubsetPure(3, T)
        \union kSubsetPure(0, T))

(*
\* This test contains expressions that are not supported by Apalache yet

TestKSubset9 ==
    LET T == 1..3
        kSubsetPure(k, S) == { s \in SUBSET S : Cardinality(s) = k }
    IN
    \A k \in 1..Cardinality(T):
        /\ ((SUBSET T) \subseteq kSubsetPure(k, T))
            <=> ((SUBSET T) \subseteq kSubset(k, T))
        /\ kSubsetPure(k, T) \subseteq (SUBSET T)
            <=> kSubset(k, T) \subseteq (SUBSET T)
 *)

TestFoldSet1 ==
    FoldSet(LAMBDA x, y: x + y, 0, 0 .. 10) = 55

TestFoldSet2 ==
    FoldSet(LAMBDA x, y: x + y, 0, { 1, 1, 2, 3, 3, 3 }) = 6

TestChooseUnique ==
    ChooseUnique({2, 3, 4, 5}, LAMBDA x : x % 3 = 1) = 4

TestSymDiff1 ==
    SymDiff({}, {}) = EmptySet

TestSymDiff2 ==
    SymDiff({1}, {}) = {1}

TestSymDiff3 ==
    SymDiff({}, {1}) = {1}

TestSymDiff4 ==
    SymDiff({}, {1,2}) = {1,2}

TestSymDiff5 ==
    SymDiff({1,2}, {}) = {1,2}

TestSymDiff6 ==
    SymDiff({1,2}, {2,3}) = {1,3}

TestSymDiff7 ==
    SymDiff({1,2,3}, {2,3,4}) = {1,4}

TestSymDiff8 ==
    SymDiff({1,2,3}, {2,3}) = {1}

TestSymDiff9 ==
    SymDiff({2,3}, {2,3,4}) = {4}

TestSumSet ==
    SumSet(1..3) = 6

TestProductSet ==
    ProductSet(1..4) = 24

AllTests ==
    /\ TestQuantify1
    /\ TestQuantify2
    /\ TestQuantify3
    /\ TestQuantify4
    /\ TestQuantify5
    /\ TestKSubset1
    /\ TestKSubset2
    /\ TestKSubset3
    /\ TestKSubset4
    /\ TestKSubset5
    /\ TestKSubset6
    /\ TestKSubset7
    /\ TestKSubset8
    /\ TestFoldSet1
    /\ TestFoldSet2
    /\ TestChooseUnique
    /\ TestSymDiff1
    /\ TestSymDiff2
    /\ TestSymDiff3
    /\ TestSymDiff4
    /\ TestSymDiff5
    /\ TestSymDiff6
    /\ TestSymDiff7
    /\ TestSymDiff8
    /\ TestSymDiff9
    /\ TestSumSet
    /\ TestProductSet

===============================================================================
