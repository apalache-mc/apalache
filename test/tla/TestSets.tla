------------------------------- MODULE TestSets -------------------------------
(*
 * Functional tests for operators over sets.
 * We introduce a trivial state machine and write tests as state invariants.
 *)

EXTENDS Integers, FiniteSets, Apalache

Init == TRUE
Next == TRUE

(* DEFINITIONS *)

\* The set { 1, 2, 3, 5, 6, 7 }
\* that has duplicates in its internal representation
Set123567 ==
    LET one == 1 IN
    LET two == 2 IN
    LET three == one + two IN
    \* 3 and three are equal but the set constructor will miss that
    { one, two, 3, three, three, 5, 6, 7, 7 }

\* The set { 1, 3, 5, 7 }
\* that has ghost cells 2, 6 in its internal representation
Set1357 ==
    { i \in Set123567: i % 2 /= 0 }

\* The set { 2, 6 }
\* that has ghost cells 1, 3, three, 5 in its internal representation
Set26 ==
    { i \in Set123567: i % 2 = 0 }

\* The set { 2, 3, 6 }
\* that has ghost cells 1, 3, three, 5 and non-ghost cells 2, 3, 6
Set263 ==
    Set26 \union { 3 }

SetEmpty ==
    \* create an empty set yet avoiding constant propagation
    LET x == 1 IN
    { 1 } \ { x }


(* TESTS *)
TestSet123567eq123567 ==
    Set123567 = { 1, 2, 3, 5, 6, 7 }

TestSet123567ne1357 ==
    Set123567 /= Set1357

TestSet123567neEmpty ==
    Set123567 /= {}

TestSet263ne26 ==
    Set263 /= Set26

TestSet263union1357 ==
    Set263 \union Set1357 = Set123567

TestSet263minus1357 ==
    Set263 \ Set1357 = Set26

TestSet263intersect1357 ==
    Set263 \intersect Set1357 = { 3 }

TestSetTimes ==
    Set26 \X Set26 = { <<2, 2>>, <<2, 6>>, <<6, 2>>, <<6, 6>> }

TestSetTimesCardinality ==
    Cardinality(Set26 \X Set26) = 4

TestCardinality123567 ==
    Cardinality(Set123567) = 6

TestCardinality1357 ==
    Cardinality(Set1357) = 4

TestCardinalityEmpty ==
    Cardinality(SetEmpty) = 0

TestCardinalitySets ==
    Cardinality({ {}, {2} , {6}, {3}, {2, 6}, {2, 3}, {3, 6}, {2, 6, 3} }) = 8

TestIn ==
    /\ 1 \in Set1357
    /\ 3 \in Set1357
    /\ 5 \in Set1357
    /\ 7 \in Set1357

TestNotIn ==
    /\ 0 \notin Set1357
    /\ 2 \notin Set1357
    /\ 4 \notin Set1357
    /\ 6 \notin Set1357
    /\ 8 \notin Set1357

TestSubseteq ==
    /\ SetEmpty \subseteq Set123567
    /\ Set123567 \subseteq Set123567
    /\ Set26 \subseteq Set263
    /\ Set263 \subseteq Set263
    /\ Set1357 \subseteq Set123567

TestNotSubseteq ==
    /\ ~(Set123567 \subseteq SetEmpty)
    /\ ~(Set123567 \subseteq Set263)
    /\ ~(Set263 \subseteq Set26)
    /\ ~(Set123567 \subseteq Set1357)

TestSetMap ==
    LET Cards == { Cardinality(S): S \in { Set1357, Set123567, SetEmpty } } IN
    Cards = { 0, 4, 6 }

TestSetMapSets ==
    LET Sets == { { i \in S: i < 5 } : S \in { Set1357, Set123567, SetEmpty } } IN
    Sets = { {}, { 1, 3 }, { 1, 2, 3 } }

\* TODO: FIX IT!
\* https://github.com/informalsystems/apalache/issues/1358
TestPowersetEmpty ==
    LET \* @type: Set(Int);
        S == {}
    IN
    SUBSET S = { {} }

\* TODO: FIX IT!
\* https://github.com/informalsystems/apalache/issues/1358
TestPowerset26 ==
    { {}, { 2 }, { 6 }, { 2, 6 } } = SUBSET Set26

\* TODO: FIX IT!
\* https://github.com/informalsystems/apalache/issues/1103
TestPowersetSubsetEq ==
    (SUBSET Set26) \subseteq SUBSET Set26

\* TODO: FIX IT!
\* https://github.com/informalsystems/apalache/issues/1339
TestExistsEmptyInPowerset ==
    \E S \in SUBSET Set263:
        S = {}

\* TODO: FIX IT!
\* https://github.com/informalsystems/apalache/issues/1339
TestExists15InPowerset ==
    \E S \in SUBSET Set263:
        S = { 2, 6 }

\* This test is expected to fail. It should be run separately.
FailExpandLargePowerset ==
    \E S \in SUBSET (1..30):
        31 \notin S

TestForallInPowerset ==
    \A S \in SUBSET Set1357:
        6 \notin S

TestPowersetCardinality ==
    Cardinality(SUBSET Set263) = 8

TestUnion ==
    UNION { Set26, Set1357, SetEmpty } = Set123567

TestUnionEmpty ==
    LET \* @type: Set(Set(Int));
        Empty == {}
    IN
    UNION Empty = {}

TestForall ==
    \A i \in Set1357:
        i = 1 \/ i = 3 \/ i = 5 \/ i = 7

TestExists ==
    \E i \in Set1357:
        i = 3

TestChooseMin ==
    LET min == CHOOSE i \in Set1357:
        \A j \in Set1357: i <= j
    IN
    min = 1

TestGuessMin ==
    LET min == Guess({
            i \in Set1357:
                \A j \in Set1357: i <= j
        })
    IN
    min = 1

TestChooseSet ==
    LET S ==
        CHOOSE T \in { SetEmpty, Set263, Set1357 }:
            6 \in T
    IN
    S = Set263

TestGuessSet ==
    LET S ==
        Guess({ T \in { SetEmpty, Set263, Set1357 }: 6 \in T })
    IN
    S = Set263

TestChooseSetFromTwo ==
    LET S ==
        CHOOSE T \in { SetEmpty, Set263, Set1357 }:
            3 \in T
    IN
    S \in { Set263, Set1357 }

TestGuessSetFromTwo ==
    LET S ==
        Guess({ T \in { SetEmpty, Set263, Set1357 }: 3 \in T })
    IN
    S \in { Set263, Set1357 }

TestChooseInSingleton ==
    LET x == CHOOSE i \in { 3 }: TRUE IN
    x = 3

TestGuessInSingleton ==
    LET x == Guess({ 3 }) IN
    x = 3

TestChooseEmpty ==
    LET x == CHOOSE i \in SetEmpty: TRUE IN
    \* This expression is equivalent to TRUE.
    \* We are using to avoid constant simplification of TRUE.
    x <= 0 \/ x > 0

TestGuessEmpty ==
    LET x == Guess(SetEmpty) IN
    \* This expression is equivalent to TRUE.
    \* We are using to avoid constant simplification of TRUE.
    x <= 0 \/ x > 0

TestForallSet ==
    \A S \in { SetEmpty, Set26, Set1357 }:
        10 \notin S

TestExistsSet ==
    \E S \in { SetEmpty, Set26, Set1357 }:
        5 \in S

TestIsFiniteSet ==
    /\ IsFiniteSet(SetEmpty)
    /\ IsFiniteSet(Set26)
    /\ IsFiniteSet(Set1357)

\* TODO: FIX IT!
\* https://github.com/informalsystems/apalache/issues/1361
TestIsFiniteSetOnInfinite ==
    /\ ~IsFiniteSet(Int)
    /\ ~IsFiniteSet(Nat)

AllTests ==
    /\ TestSet123567eq123567
    /\ TestSet123567ne1357
    /\ TestSet123567neEmpty
    /\ TestSet263ne26
    /\ TestSet263union1357
    /\ TestSet263minus1357
    /\ TestSet263intersect1357
    /\ TestSetTimes
    /\ TestSetTimesCardinality
    /\ TestCardinality123567
    /\ TestCardinality1357
    /\ TestCardinalityEmpty
    /\ TestCardinalitySets
    /\ TestIn
    /\ TestNotIn
    /\ TestSubseteq
    /\ TestNotSubseteq
    /\ TestSetMap
    /\ TestSetMapSets
    /\ TestForallInPowerset
    /\ TestUnion
    /\ TestUnionEmpty
    /\ TestForall
    /\ TestExists
    /\ TestForallSet
    /\ TestExistsSet
    /\ TestChooseMin
    /\ TestChooseInSingleton
    /\ TestChooseEmpty
    /\ TestChooseSet
    /\ TestGuessMin
    /\ TestGuessInSingleton
    /\ TestGuessEmpty
    /\ TestGuessSet
    /\ TestIsFiniteSet
    /\ TestPowersetCardinality
    \* IGNORE UNTIL FIXED: /\ TestIsFiniteSetOnInfinite
    \* IGNORE UNTIL FIXED: /\ TestPowersetEmpty
    \* IGNORE UNTIL FIXED: /\ TestPowerset26
    \* IGNORE UNTIL FIXED: /\ TestPowersetSubsetEq
    \* IGNORE UNTIL FIXED: /\ TestExistsEmptyInPowerset
    \* IGNORE UNTIL FIXED: /\ TestExists15InPowerset

===============================================================================
