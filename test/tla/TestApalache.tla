---------------------------- MODULE TestApalache -----------------------------
(*
 * Test the module Apalache against TLC.
 *
 * Igor Konnov, 2026
 *)

EXTENDS Sequences, Integers, Apalache

VARIABLE
    \* This is needed for TLC to work
    \* @type: Int;
    xxx

Init == xxx = 0
Next == UNCHANGED xxx

(********************* DEFINITIONS ********************************)
\* @type: Seq(Int);
seq345 == <<3, 4, 5>>

\* @type: Seq(Int);
seqEmpty == <<>>

\* @type: Seq(Int);
seq26970 == <<2, 6, 9, 7, 0>>

Add(i, j) == i + j

IsOdd(i) == i % 2 = 1

Concat(s, t) == s \o t

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

(********************* TESTS ********************************)

TestFoldSeq26970 ==
    ApaFoldSeqLeft(Add, 0, seq26970) = 2 + 6 + 9 + 7

TestFoldSeq697 ==
    ApaFoldSeqLeft(Add, 0, SubSeq(seq26970, 2, 4)) = 6 + 9 + 7

TestFoldSeq345 ==
    ApaFoldSeqLeft(Add, 0, Tail(seq345)) = 4 + 5

TestFoldSeqEmpty ==
    ApaFoldSeqLeft(Add, 0, seqEmpty) = 0

TestFoldSeqFlatten ==
    ApaFoldSeqLeft(Concat, <<>>, <<seq345, seqEmpty, seq26970>>) = <<3, 4, 5, 2, 6, 9, 7, 0>>

TestMkSeqDouble ==
    LET Double(i) == 2 * i IN
    MkSeq(4, Double) = <<2, 4, 6, 8>>

TestMkSeqEmpty ==
    LET Double(i) == 2 * i IN
    MkSeq(0, Double) = << >>

TestMkSeqConcat ==
    LET Double(i) == 2 * i IN
    LET Triple(i) == 3 * i IN
    MkSeq(2, Double) \o MkSeq(3, Triple) = <<2, 4, 3, 6, 9>>

TestMkSeqSubSeq ==
    LET Triple(i) == 3 * i IN
    SubSeq(MkSeq(5, Triple), 2, 3) = <<6, 9>>

TestMkSeqLen ==
    LET Double(i) == 2 * i IN
    Len(MkSeq(4, Double)) = 4

TestMkSeqFold ==
    LET Double(i) == 2 * i IN
    ApaFoldSeqLeft(Add, 0, MkSeq(4, Double)) = 20

TestFoldSeqOverSelectSeq ==
    ApaFoldSeqLeft(Add, 0, SelectSeq(seq345, IsOdd)) = 3 + 5

TestFunAsSeq3 ==
    LET f == [ i \in 1..3 |-> i + 1 ] IN
    FunAsSeq(f, 3, 3) = <<2, 3, 4>>

TestFunAsSeqEmpty ==
    LET
        \* @type: Int -> Int;
        f == [ i \in {} |-> i ]
    IN
    FunAsSeq(f, 0, 0) = << >>

\* TLC fails here, so we do not include this test
TestFunAsSeqLargerCapacity ==
    LET f == [ i \in 1..3 |-> i + 1 ] IN
    \* provide a larger upper bound
    FunAsSeq(f, 3, 10) = <<2, 3, 4>>

TestGuessSet ==
    LET S ==
        Guess({ T \in { SetEmpty, Set263, Set1357 }: 6 \in T })
    IN
    S = Set263

TestGuessSetFromTwo ==
    LET S ==
        Guess({ T \in { SetEmpty, Set263, Set1357 }: 3 \in T })
    IN
    S \in { Set263, Set1357 }

TestGuessInSingleton ==
    LET x == Guess({ 3 }) IN
    x = 3

TestGuessEmpty ==
    LET x == Guess(SetEmpty) IN
    \* This expression is equivalent to TRUE.
    \* We are using to avoid constant simplification of TRUE.
    x <= 0 \/ x > 0

TestApaFoldSet ==
    LET \* @type: (Set(Int), Int) => Set(Int);
        A(p,q) == p \union {q}
    IN
    ApaFoldSet( A, {4,4}, {1,1,2,2,3,3} ) = {1,2,3,4}

\* this test is a disjunction of all smaller tests
AllTests ==
    /\ TestFoldSeq26970
    /\ TestFoldSeq697
    /\ TestFoldSeq345
    /\ TestFoldSeqEmpty
    /\ TestFoldSeqFlatten
    /\ TestFoldSeqOverSelectSeq
    /\ TestMkSeqDouble
    /\ TestMkSeqEmpty
    /\ TestMkSeqConcat
    /\ TestMkSeqSubSeq
    /\ TestMkSeqLen
    /\ TestMkSeqFold
    /\ TestFunAsSeq3
    /\ TestFunAsSeqEmpty
    /\ TestGuessSet
    /\ TestGuessSetFromTwo
    /\ TestGuessInSingleton
    /\ TestApaFoldSet
    \* TLC fails here
    \*/\ TestGuessEmpty
    \*/\ TestFunAsSeqLargerCapacity

===============================================================================
