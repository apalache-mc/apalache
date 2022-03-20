----------------------- MODULE TestSequencesExt -----------------------------
(*
 * The purpose of this test is to make sure that all sequence operators are
 * working as expected. Hence, we write down a trivial state machine and write
 * all tests as state invariants.
 *)

EXTENDS Sequences, FiniteSets, SequencesExt, Integers, Apalache

Init == TRUE

Next == TRUE

(********************* USEFUL DEFINITIONS ********************************)
\* @type: Seq(Int);
seq345 == <<3, 4, 5>>

\* @type: Seq(Int);
intSeqEmpty == <<>>

\* @type: Seq(Str);
strSeqEmpty == <<>>

\* @type: Set(Int);
setEmpty == {}

\* @type: Seq(Int);
seq26970 == <<2, 6, 9, 7, 0>>

Add(i, j) == i + j

IsOdd(i) == i % 2 = 1

Concat(s, t) == s \o t

(********************* TESTS ********************************)
TestToSet1 ==
    ToSet(intSeqEmpty) = setEmpty

TestToSet2 ==
    ToSet(<<1>>) = {1}

TestToSet3 ==
    ToSet(<<1, 1>>) = {1}

TestToSet4 ==
    ToSet(<<1, 2, 3>>) = {1, 2, 3}

TestToSet5 ==
    ToSet(<<1, 2, 3>>) = {1, 2, 3}

TestToSet6 ==
    ToSet(FunAsSeq([i \in 1..10 |-> 42], 10, 10)) = { 42 }

TestToSet7 ==
    ToSet(FunAsSeq([i \in 1..10 |-> i], 10, 10)) = 1..10

TestToSet8 ==
    ToSet(Tail(FunAsSeq([i \in 1..10 |-> i], 10, 10))) = 2..10

TestToSet9 ==
    ToSet(FunAsSeq([i \in 0..9 |-> 42], 10, 10)) = { 42 }

TestSetToSeq1 ==
    SetToSeq(setEmpty) = intSeqEmpty

TestSetToSeq2 ==
    SetToSeq({1}) = <<1>>

TestSetToSeq3 ==
    LET s == {"t", "l", "a", "p", "l", "u", "s"}
        seq == SetToSeq(s)
    IN
    /\ Len(seq) = Cardinality(s)
    /\ ToSet(seq) = s

TestSetToSortSeq ==
    LET charToInt ==
        SetAsFun({
            <<"a", 1>>, <<"c", 3>>, <<"e", 5>>,
            <<"h", 8>>, <<"l", 12>>, <<"p", 16>>
        })
    IN
    LET LessThan(a, b) == charToInt[a] < charToInt[b] IN
    LET s == {"a", "p", "a", "l", "a", "c", "h", "e"}
        seq == SetToSortSeq(s, LessThan)
    IN
    \*/\ Len(seq) = Cardinality(s)
    \*/\ ToSet(seq) = s
    /\ seq = <<"a", "c", "e", "h", "l", "p">>

TestContains1 ==
    ~Contains(intSeqEmpty, 3)

TestContains2 ==
    Contains(<<3>>, 3)

TestContains3 ==    
    ~Contains(<<3>>, 4)

TestContains4 ==    
    Contains(<<3,4>>, 3)

TestContains5 ==
    Contains(<<3,4>>, 4)

TestContains6 ==
    Contains(<<{3},{4}>>, {4})

TestContains7 ==
    Contains(<<{3},{4}>>, {3})

TestContains8 ==
    ~Contains(<<{3},{4}>>, {2})

TestReverse1 ==
    Reverse(intSeqEmpty) = intSeqEmpty

TestReverse2 ==
    Reverse(<<1,2,3>>) = <<3,2,1>>

TestReverse3 ==
    Reverse(<<1,1,2>>) = <<2,1,1>>

TestReverse4 ==
    Reverse(<<"a","a","b">>) = <<"b","a","a">>

TestRemove1 ==
    Remove(strSeqEmpty, "c") = strSeqEmpty

TestRemove2 ==
    Remove(<<"a","a","b">>, "a") = <<"b">>

TestRemove3 ==
    Remove(<<"a","a","a">>, "a") = strSeqEmpty

TestRemove4 ==
    Remove(<<"a","a","b">>, "c") = <<"a","a","b">>

TestRemove5 ==
    Remove(<<{"a", "b"}, {"a","c"}>>, {"c", "a"}) = <<{"a", "b"}>>

TestReplaceAll1 ==
    ReplaceAll(intSeqEmpty, 1, 4) = intSeqEmpty

TestReplaceAll2 ==
    ReplaceAll(<<1, 1, 2, 1, 1, 3>>, 1, 4) = <<4, 4, 2, 4, 4, 3>>

TestInsertAt1 ==
    InsertAt(<<1, 2, 3>>, 2, 10) = <<1, 10, 2, 3>>

TestInsertAt2 ==
    InsertAt(<<1, 2, 3>>, 1, 10) = <<10, 1, 2, 3>>

TestInsertAt3 ==
    InsertAt(<<1, 2, 3>>, 3, 10) = <<1, 2, 10, 3>>

TestInsertAt4 ==
    InsertAt(<<1, 2, 3>>, 4, 10) = <<1, 2, 3, 10>>

TestRemoveAt1 ==
    RemoveAt(<<1, 2, 3>>, 2) = <<1, 3>>

TestRemoveAt2 ==
    RemoveAt(<<1, 2, 3>>, 1) = <<2, 3>>

TestRemoveAt3 ==
    RemoveAt(<<1, 2, 3>>, 3) = <<1, 2>>

TestRemoveAt4 ==
    RemoveAt(<<1, 2, 3>>, 4) = <<1, 2, 3>>

TestReplaceAt1 ==
    ReplaceAt(<<1>>, 1, 2) = <<2>>

TestReplaceAt2 ==
    ReplaceAt(<<1, 1, 1>>, 1, 2) = <<2, 1, 1>>

TestCons1 ==
    Cons(3, <<2, 4>>) = <<3, 2, 4>>

TestFront1 ==
    Front(<<3, 4, 5>>) = <<3, 4>>

TestLast1 ==
    Last(<<3, 4, 5>>) = 5

TestPrefix1 ==
    IsPrefix(intSeqEmpty, intSeqEmpty)

TestPrefix2 ==
    IsPrefix(intSeqEmpty, <<1>>)

TestPrefix3 ==
    IsPrefix(<<1>>, <<1,2>>)

TestPrefix4 ==
    IsPrefix(<<1,2>>, <<1,2>>)

TestPrefix5 ==
    IsPrefix(<<1,2>>, <<1,2,3>>)

TestPrefix6 ==
    ~IsPrefix(<<1,2,3>>, <<1,2>>)

TestPrefix7 ==
    ~IsPrefix(<<1,2,2>>, <<1,2,3>>)

TestPrefix8 ==
    ~IsPrefix(<<1,2,3>>, <<1,2,2>>)

TestPrefix9 ==
    ~IsPrefix(<<1>>, <<2>>)

TestPrefix10 ==
    ~IsPrefix(<<2>>, <<1>>)

TestPrefix11 ==
    ~IsPrefix(<<2,1>>, <<1,2>>)

TestPrefix12 ==
    ~IsPrefix(<<1,2>>, <<2,1>>)

TestIsStrictPrefix1 ==
    ~IsStrictPrefix(intSeqEmpty, intSeqEmpty)

TestIsStrictPrefix2 ==
    IsStrictPrefix(intSeqEmpty, <<1>>)

TestIsStrictPrefix3 ==
    IsStrictPrefix(<<1>>, <<1,2>>)

TestIsStrictPrefix4 ==
    ~IsStrictPrefix(<<1,2>>, <<1,2>>)

TestIsStrictPrefix5 ==
    IsStrictPrefix(<<1,2>>, <<1,2,3>>)

TestSuffix1 ==
    IsSuffix(<<3>>, <<1,2,3>>)

TestSuffix2 ==
    IsSuffix(<<2,3>>, <<1,2,3>>)

TestSuffix3 ==
    ~IsSuffix(<<3,2>>, <<1,2,3>>)

TestSuffix4 ==
    IsSuffix(<<1,2,3>>, <<1,2,3>>)

TestIsStrictSuffix1 ==
    ~IsStrictSuffix(<<1,2,3>>, <<1,2,3>>)

\* this test is a disjunction of all smaller tests
AllTests ==
    /\ TestSetToSeq1
    /\ TestSetToSeq2
    /\ TestSetToSeq3
    \*/\ TestSetToSortSeq
    /\ TestToSet1
    /\ TestToSet2
    /\ TestToSet3
    /\ TestToSet4
    /\ TestToSet5
    /\ TestToSet6
    /\ TestToSet7
    /\ TestToSet8
    /\ TestToSet9
    /\ TestContains1
    /\ TestContains2
    /\ TestContains3
    /\ TestContains4
    /\ TestContains5
    /\ TestContains6
    /\ TestContains7
    /\ TestContains8
    /\ TestReverse1
    /\ TestReverse2
    /\ TestReverse3
    /\ TestReverse4
    (*
    /\ TestRemove1
    /\ TestRemove2
    /\ TestRemove3
    /\ TestRemove4
    /\ TestRemove5
    *)
    /\ TestReplaceAll1
    /\ TestReplaceAll2
    (*
    /\ TestInsertAt1
    /\ TestInsertAt2
    /\ TestInsertAt3
    /\ TestInsertAt4
    *)
    /\ TestReplaceAt1
    /\ TestReplaceAt2
    /\ TestRemoveAt1
    /\ TestRemoveAt2
    /\ TestRemoveAt3
    /\ TestRemoveAt4
    /\ TestCons1
    /\ TestFront1
    /\ TestLast1
    /\ TestPrefix1
    /\ TestPrefix2
    /\ TestPrefix3
    /\ TestPrefix4
    /\ TestPrefix5
    /\ TestPrefix6
    /\ TestPrefix7
    /\ TestPrefix8
    /\ TestPrefix9
    /\ TestPrefix10
    /\ TestPrefix11
    /\ TestPrefix12
    /\ TestIsStrictPrefix1
    /\ TestIsStrictPrefix2
    /\ TestIsStrictPrefix3
    /\ TestIsStrictPrefix4
    /\ TestIsStrictPrefix5
    /\ TestSuffix1
    /\ TestSuffix2
    /\ TestSuffix3
    /\ TestSuffix4
    /\ TestIsStrictSuffix1

===============================================================================
