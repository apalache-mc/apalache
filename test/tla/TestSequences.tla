---------------------------- MODULE TestSequences -----------------------------
(*
 * The purpose of this test is to make sure that all sequence operators are
 * working as expected. Hence, we write down a trivial state machine and write
 * all tests as state invariants.
 *)

EXTENDS Sequences, Integers, Apalache

Init == TRUE

Next == TRUE

(********************* USEFUL DEFINITIONS ********************************)
\* @type: Seq(Int);
seq345 == <<3, 4, 5>>

\* @type: Seq(Int);
seqEmpty == <<>>

\* @type: Seq(Int);
seq26970 == <<2, 6, 9, 7, 0>>

Add(i, j) == i + j

IsOdd(i) == i % 2 = 1

Concat(s, t) == s \o t

(********************* TESTS ********************************)

\* we cannot report a static error here, as it may ruin a formula
TestHeadEmpty ==
    \* wrap into a set to trick the simplifier
    { Head(seqEmpty) } /= {} \* Head(<<>>) is undefined

\* we cannot report a static error here, as it may ruin a formula
TestTailEmpty ==
    \* wrap into a set to trick the simplifier
    { Tail(seqEmpty) } /= {} \* Tail(<<>>) is undefined

\* we cannot report a static error here, as it may ruin a formula
TestApply0 ==
    \* wrap into a set to trick the simplifier
    { seq345[0] } /= {} \* out of bounds

\* we cannot report a static error here, as it may ruin a formula
TestApply4 ==
    \* wrap into a set to trick the simplifier
    { seq345[4] } /= {} \* out of bounds

TestApplyNonStatic4 ==
    \* this query requires the solver
    \E i \in DOMAIN seq345:
        seq345[i] = 4

TestApplyNonStatic9 ==
    \* this query requires the solver
    \A i \in DOMAIN seq345:
        seq345[i] /= 9

TestCtorEmpty ==
    Len(seqEmpty) = 0

TestCtor345 ==
    /\ seq345[1] = 3 /\ seq345[2] = 4 /\ seq345[3] = 5
    /\ Len(seq345) = 3

TestDomainEmpty ==
    DOMAIN seqEmpty = {}

TestDomain345 ==
    DOMAIN seq345 = { 1, 2, 3 }

TestHead345 ==
    Head(seq345) = 3

TestSubSeq345to45 ==
    /\ SubSeq(seq345, 2, 3) = <<4, 5>>
    /\ Len(SubSeq(seq345, 2, 3)) = 2

TestSubSeq345to3 ==
    /\ SubSeq(seq345, 1, 1) = <<3>>
    /\ Len(SubSeq(seq345, 1, 1)) = 1

TestSubSeq345to5 ==
    /\ SubSeq(seq345, 3, 3) = <<5>>
    /\ Len(SubSeq(seq345, 3, 3)) = 1

TestSubSeq345toEmpty ==
    /\ SubSeq(seq345, 3, 0) = <<>>
    /\ Len(SubSeq(seq345, 3, 0)) = 0

TestAppend345and6 ==
    /\ Append(seq345, 6) = <<3, 4, 5, 6>>
    /\ Len(Append(seq345, 6)) = 4

TestAppendEmptyAnd6 ==
    /\ Append(seqEmpty, 6) = <<6>>
    /\ Len(Append(seqEmpty, 6)) = 1

TestAppend6toSubseq ==
    /\ Append(SubSeq(seq345, 2, 3), 6) = <<4, 5, 6>>
    /\ Len(Append(SubSeq(seq345, 2, 3), 6)) = 3

TestAppend6toTail ==
    /\ Append(Tail(seq345), 6) = <<4, 5, 6>>
    /\ Len(Append(Tail(seq345), 6)) = 3

TestAppendHeadtoTail ==
    /\ Append(Tail(seq345), Head(seq345)) = <<4, 5, 3>>
    /\ Len(Append(Tail(seq345), Head(seq345))) = 3

TestConcat345and345 ==
    /\ seq345 \o seq345 = <<3, 4, 5, 3, 4, 5>>
    /\ Len(seq345 \o seq345) = 6

TestConcat345and45 ==
    /\ seq345 \o Tail(seq345) = <<3, 4, 5, 4, 5>>
    /\ Len(seq345 \o Tail(seq345)) = 5

TestExists ==
    \E seq \in { seq345, seqEmpty, seq26970 }:
        3 \in DOMAIN seq /\ seq[3] = 9

TestForAll ==
    \A seq \in { seq345, seqEmpty, seq26970 }:
        (2 \in DOMAIN seq) => (seq[2] /= 5)

TestFoldSeq26970 ==
    ApaFoldSeqLeft(Add, 0, seq26970) = 2 + 6 + 9 + 7

TestFoldSeq697 ==
    ApaFoldSeqLeft(Add, 0, SubSeq(seq26970, 2, 4)) = 6 + 9 + 7

TestFoldSeq345 ==
    ApaFoldSeqLeft(Add, 0, Tail(seq345)) = 4 + 5

TestFoldSeqEmpty ==
    ApaFoldSeqLeft(Add, 0, Tail(seqEmpty)) = 0

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

TestSelectSeq345 ==
    SelectSeq(seq345, IsOdd) = <<3, 5>>

TestSelectSeqEmpty ==
    SelectSeq(seqEmpty, IsOdd) = seqEmpty

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

TestFunAsSeqLargerCapacity ==
    LET f == [ i \in 1..3 |-> i + 1 ] IN
    \* provide a larger upper bound
    FunAsSeq(f, 3, 10) = <<2, 3, 4>>

TestExceptLen ==
    Len([seq345 EXCEPT ![2] = 10]) = 3

TestExceptDomain ==
    DOMAIN [seq345 EXCEPT ![2] = 10] = DOMAIN seq345

TestSubSeqEq ==
    SubSeq(<<"a", "b", "c">>, 1, 2) = SubSeq(<<"a", "b", "d">>, 1, 2)

TestSubSeqNeq ==
    SubSeq(<<"a", "b", "c">>, 1, 3) /= SubSeq(<<"a", "b", "d">>, 1, 3)

\* this test is a disjunction of all smaller tests
AllTests ==
    /\ TestHeadEmpty
    /\ TestTailEmpty
    /\ TestApply0
    /\ TestApply4
    /\ TestApplyNonStatic4
    /\ TestApplyNonStatic9
    /\ TestCtorEmpty
    /\ TestCtor345
    /\ TestDomainEmpty
    /\ TestDomain345
    /\ TestHead345
    /\ TestSubSeq345to45
    /\ TestSubSeq345to3
    /\ TestSubSeq345to5
    /\ TestSubSeq345toEmpty
    /\ TestAppend345and6
    /\ TestAppendEmptyAnd6
    /\ TestAppend6toSubseq
    /\ TestAppend6toTail
    /\ TestAppendHeadtoTail
    /\ TestConcat345and345
    /\ TestConcat345and45
    /\ TestExists
    /\ TestForAll
    /\ TestFoldSeq26970
    /\ TestFoldSeq697
    /\ TestFoldSeq345
    /\ TestFoldSeqEmpty
    /\ TestFoldSeqFlatten
    /\ TestSelectSeq345
    /\ TestSelectSeqEmpty
    /\ TestFoldSeqOverSelectSeq
    /\ TestMkSeqDouble
    /\ TestMkSeqEmpty
    /\ TestMkSeqConcat
    /\ TestMkSeqSubSeq
    /\ TestMkSeqLen
    /\ TestMkSeqFold
    /\ TestFunAsSeq3
    /\ TestFunAsSeqEmpty
    /\ TestFunAsSeqLargerCapacity
    /\ TestExceptLen
    /\ TestExceptDomain
    /\ TestSubSeqEq
    /\ TestSubSeqNeq

===============================================================================
