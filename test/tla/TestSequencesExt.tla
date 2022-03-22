----------------------- MODULE TestSequencesExt -----------------------------
(*
 * The purpose of this test is to make sure that all sequence operators are
 * working as expected. Hence, we write down a trivial state machine and write
 * all tests as state invariants.
 *)

EXTENDS Sequences, FiniteSets, SequencesExt, Integers

A == INSTANCE Apalache

Init == TRUE

Next == TRUE

(********************* USEFUL DEFINITIONS ********************************)
\* @type: Seq(Int);
seq345 == <<3, 4, 5>>

\* @type: Seq(Int);
intSeqEmpty == <<>>

\* @type: Seq(Seq(Int));
intSeqSeqEmpty == <<>>

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
    ToSet(A!FunAsSeq([i \in 1..10 |-> 42], 10, 10)) = { 42 }

TestToSet7 ==
    ToSet(A!FunAsSeq([i \in 1..10 |-> i], 10, 10)) = 1..10

TestToSet8 ==
    ToSet(Tail(A!FunAsSeq([i \in 1..10 |-> i], 10, 10))) = 2..10

TestToSet9 ==
    ToSet(A!FunAsSeq([i \in 0..9 |-> 42], 10, 10)) = { 42 }

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
        A!SetAsFun({
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

TestPrefixes1 ==
    Prefixes(<<"a", "b", "c">>) =
        {<<>>, <<"a">>, <<"a", "b">>, <<"a", "b", "c">>}

TestPrefixes2 ==
    LET \* @type: Set(Seq(Str));
        S == {<<"a", "b", "c">>, <<"a", "b", "d">>}
    IN
    LET P == UNION { Prefixes(seq) : seq \in S } IN
    P = {<<>>, <<"a">>, <<"a", "b">>, <<"a", "b", "c">>, <<"a", "b", "d">>}

TestPrefixes3 ==
    LET S1 == {<<>>, <<"a">>, <<"a", "b">>, <<"a", "b", "c">>} IN
    LET S2 == {<<>>, <<"a">>, <<"a", "b">>, <<"a", "b", "d">>} IN
    LET P == UNION { S1, S2 } IN
    P = {<<>>, <<"a">>, <<"a", "b">>, <<"a", "b", "c">>, <<"a", "b", "d">>}

TestCommonPrefixes1 ==
    CommonPrefixes({<<"a", "b", "c">>, <<"a", "b", "d">>})
        = {<<>>, <<"a">>, <<"a", "b">>}

TestLongestCommonPrefix1 ==
    LongestCommonPrefix({<<"a", "b", "c">>, <<"a", "b", "d">>}) = <<"a", "b">>

TestLongestCommonPrefix2 ==
    LongestCommonPrefix({<<"a", "b", "c">>, <<"a">>}) = <<"a">>

TestLongestCommonPrefix3 ==
    LongestCommonPrefix({strSeqEmpty}) = strSeqEmpty

TestLongestCommonPrefix4 ==
    LongestCommonPrefix({<<"a">>, <<"b">>}) = strSeqEmpty

TestLongestCommonPrefix5 ==
    LongestCommonPrefix({<<"a", "b", "c">>,
        <<"a", "b", "c", "c">>, <<"a", "b", "c", "d">>}) = <<"a", "b", "c">>

TestFoldSeq1 ==
    LET __plus_one(e, acc) == acc + e IN
    FoldSeq(__plus_one, 0, <<1, 2, 1, 3, 1>>) = 8

TestFoldLeft1 ==
    LET __plus_one(acc, e) == acc + e IN
    FoldLeft(__plus_one, 0, <<1, 2, 1, 3, 1>>) = 8

TestFoldRight1 ==
    LET __plus(e, acc) == acc + e IN
    FoldRight(__plus, <<1, 2, 1, 3, 1>>, 0) = 8

TestFlattenSeq1 ==
    FlattenSeq(intSeqSeqEmpty) = <<>>

TestFlattenSeq2 ==
    FlattenSeq(<< <<1, 2>>, <<1>> >>) = << 1, 2, 1 >>

\* an original test in the community modules, which is not well-typed
(*
TestFlattenSeq3 ==
    FlattenSeq(<< <<1, 2>>, << << 1, 2 >> >> >>) = << 1, 2, << 1, 2 >> >>
 *)

TestFlattenSeq3 ==
    FlattenSeq(<< << {1}, {2} >>, << {1}, {2}, {3}>> >>)
        = << {1}, {2}, {1}, {2}, {3}>>

TestFlattenSeq4 ==
    FlattenSeq(intSeqSeqEmpty) = <<>>

TestFlattenSeq5 ==
    FlattenSeq(<< <<"a">>, <<"b">> >>) = <<"a", "b">>

\* an original test in the community modules, which is not well-typed
(*
TestFlattenSeq6 ==
    FlattenSeq(<<"a", "b">>) = "ab"
 *)

TestZip1 ==
    LET \* @type: Seq(<<Int, Int>>);
        int2SeqEmpty == <<>>
    IN
    Zip(intSeqEmpty, intSeqEmpty) = int2SeqEmpty

TestZip2 ==
    LET \* @type: Seq(<<Int, Int>>);
        int2SeqEmpty == <<>>
    IN
    Zip(intSeqEmpty, <<1>>) = int2SeqEmpty

TestZip3 ==
    LET \* @type: Seq(<<Int, Int>>);
        int2SeqEmpty == <<>>
    IN
    Zip(<<1>>, intSeqEmpty) = int2SeqEmpty

TestZip4 ==
    Zip(<<2>>, <<2>>) = << <<2, 2>> >>

TestZip5 ==
    Zip(<<2>>, <<3>>) = << <<2, 3>> >>

TestZip6 ==
    Zip(<<2, 3>>, <<1, 4>>) = << <<2, 1>>, <<3, 4>> >>

TestZip7 ==
    Zip(<<2, 3>>, <<2, 3>>) = << <<2, 2>>, <<3, 3>> >>

TestZip8 ==
    Zip(<<1, 3>>, <<2, 4>>) = <<<<1, 2>>, <<3, 4>>>>

TestZip9 ==
    Zip(<<"a", "c">>, <<"b", "d">>) = <<<<"a", "b">>, <<"c", "d">>>>

TestSubSeqs1 ==
    SubSeqs(intSeqEmpty) = {<<>>}

TestSubSeqs2 ==
    SubSeqs(<<1>>) = {<<>>, <<1>>}

TestSubSeqs3 ==
    SubSeqs(<<1, 1>>) = {<<>>, <<1>>, <<1, 1>>}

TestSubSeqs4 ==
    SubSeqs(<<1, 1, 1>>) = {<<>>, <<1>>, <<1, 1>>, <<1, 1, 1>>}

TestSubSeqs5 ==
    SubSeqs(<<1, 2, 3, 2>>) = {
        <<>>, <<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 3>>,
        <<3, 2>>, <<1, 2, 3>>, <<2, 3, 2>>, <<1, 2, 3, 2>>
    }

TestSubSeqs6 ==
    SubSeqs(<<1, 2, 3>>) = {
        <<>>, <<1>>, <<2>>, <<3>>, <<1, 2>>, <<2, 3>>, <<1, 2, 3>>
    }

\* this test is a disjunction of all smaller tests
AllTests ==
    /\ TestSetToSeq1
    /\ TestSetToSeq2
    /\ TestSetToSeq3
    (* FAILING tests:
    /\ TestSetToSortSeq
     *)
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
    (* FAILING tests:
    /\ TestRemove1
    /\ TestRemove2
    /\ TestRemove3
    /\ TestRemove4
    /\ TestRemove5
    *)
    /\ TestReplaceAll1
    /\ TestReplaceAll2
    (* FAILING tests:
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
    /\ TestPrefixes1
    /\ TestPrefixes2
    /\ TestPrefixes3
    (* FAILING tests:
    /\ TestCommonPrefixes1
    /\ TestLongestCommonPrefix1
    /\ TestLongestCommonPrefix2
    /\ TestLongestCommonPrefix3
    /\ TestLongestCommonPrefix4
    /\ TestLongestCommonPrefix5
    *)
    /\ TestFoldSeq1
    /\ TestFoldLeft1
    /\ TestFoldRight1
    /\ TestFlattenSeq1
    /\ TestFlattenSeq2
    \* FAILING TEST:
    \*/\ TestFlattenSeq3
    /\ TestFlattenSeq4
    /\ TestFlattenSeq5
    /\ TestZip1
    /\ TestZip2
    /\ TestZip3
    /\ TestZip4
    /\ TestZip5
    /\ TestZip6
    /\ TestZip7
    /\ TestZip8
    /\ TestZip9
    /\ TestSubSeqs1
    /\ TestSubSeqs2
    /\ TestSubSeqs3
    /\ TestSubSeqs4
    /\ TestSubSeqs5
    /\ TestSubSeqs6

===============================================================================
