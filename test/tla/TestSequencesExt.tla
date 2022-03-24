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
intSeqEmpty == <<>>

\* @type: Seq(Seq(Int));
intSeqSeqEmpty == <<>>

\* @type: Seq(Str);
strSeqEmpty == <<>>

\* @type: Set(Int);
setEmpty == {}

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

TestSetToSeq4 ==
  LET input == { 5, 1, 3, 3, 2, 4, 4, 1 } IN
  LET output == SetToSeq(input) IN
  ToSet(output) = input

TestSetToSortSeq1 ==
    LET charToInt ==
        A!SetAsFun({
            <<"a", 1>>, <<"c", 3>>, <<"e", 5>>,
            <<"h", 8>>, <<"l", 12>>, <<"p", 16>>
        })
    IN
    LET LessThan(a, b) == charToInt[a] < charToInt[b] IN
    LET input == { "a", "p", "l", "c", "h", "e" }
        output == SetToSortSeq(input, LessThan)
    IN
    /\ ToSet(output) = input
    /\ output = <<"a", "c", "e", "h", "l", "p">>

TestSetToSortSeq2 ==
    LET charToInt ==
        A!SetAsFun({
            <<"a", 1>>, <<"c", 3>>, <<"e", 5>>,
            <<"h", 8>>, <<"l", 12>>, <<"p", 16>>
        })
    IN
    LET LessThan(a, b) == charToInt[a] < charToInt[b] IN
    LET input == { "a", "p", "a", "l", "a", "c", "h", "e" }
        output == SetToSortSeq(input, LessThan)
    IN
    /\ ToSet(output) = input
    /\ output = <<"a", "c", "e", "h", "l", "p">>

TestSetToSortSeq3 ==
    LET \* @type: Seq(Int);
        input == <<4, 7, 9, 12, 15>>
    IN
    LET SeqRange ==
        { input[i]: i \in DOMAIN input }
    IN
    LET index ==
        [ j \in SeqRange |-> CHOOSE i \in DOMAIN input: input[i] = j ]
    IN
    LET LessThan(i, j) ==
        index[i] < index[j]
    IN
    LET output ==
        SetToSortSeq(SeqRange, LessThan)
    IN
    output = input

TestSetToSortSeq4 ==
    LET LessThan(i, j) == i < j IN
    LET input == { 5, 1, 3, 3, 2, 4, 4, 1 }
        output == SetToSortSeq(input, LessThan)
    IN
    /\ ToSet(output) = input
    /\ output = <<1, 2, 3, 4, 5>>

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
    Remove(<<"a", "a", "b">>, "a") = <<"b">>

TestRemove3 ==
    Remove(<<"a", "a", "a">>, "a") = strSeqEmpty

TestRemove4 ==
    Remove(<<"a", "a", "b">>, "c") = <<"a", "a", "b">>

TestRemove5 ==
    Remove(<<{"a", "b"}, {"a", "c"}>>, {"c", "a"}) = <<{"a", "b"}>>

TestRemove6 ==
    Remove(intSeqEmpty, 1) = intSeqEmpty

TestRemove7 ==
    Remove(<<1, 1, 2>>, 1) = <<2>>

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

TestIsPrefix1 ==
    IsPrefix(intSeqEmpty, intSeqEmpty)

TestIsPrefix2 ==
    IsPrefix(intSeqEmpty, <<1>>)

TestIsPrefix3 ==
    IsPrefix(<<1>>, <<1,2>>)

TestIsPrefix4 ==
    IsPrefix(<<1,2>>, <<1,2>>)

TestIsPrefix5 ==
    IsPrefix(<<1,2>>, <<1,2,3>>)

TestIsPrefix6 ==
    ~IsPrefix(<<1,2,3>>, <<1,2>>)

TestIsPrefix7 ==
    ~IsPrefix(<<1,2,2>>, <<1,2,3>>)

TestIsPrefix8 ==
    ~IsPrefix(<<1,2,3>>, <<1,2,2>>)

TestIsPrefix9 ==
    ~IsPrefix(<<1>>, <<2>>)

TestIsPrefix10 ==
    ~IsPrefix(<<2>>, <<1>>)

TestIsPrefix11 ==
    ~IsPrefix(<<2,1>>, <<1,2>>)

TestIsPrefix12 ==
    ~IsPrefix(<<1,2>>, <<2,1>>)

TestIsPrefix13 ==
    ~IsPrefix(<<"a", "b", "c">>, <<"a", "b", "d">>)

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

TestIsSuffix1 ==
    IsSuffix(<<3>>, <<1,2,3>>)

TestIsSuffix2 ==
    IsSuffix(<<2,3>>, <<1,2,3>>)

TestIsSuffix3 ==
    ~IsSuffix(<<3,2>>, <<1,2,3>>)

TestIsSuffix4 ==
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

TestPrefixes4 ==
    LET \* @type: Set(Seq(Str));
        S == { <<"a", "b", "c">>, <<"a", "b", "d">> } IN
    LET \* @type: Set(Seq(Str));
        P == {
            <<>>, <<"a">>, <<"a", "b">>, <<"a", "b", "c">>, <<"a", "b", "d">>
        }
    IN
    { __prefix \in P: \A __t \in S: IsPrefix(__prefix, __t) }
        = { <<>>, <<"a">>, <<"a", "b">> }

TestPrefixes5 ==
    LET \* @type: Seq(Str);
        S1 == <<"a", "b", "c">>
        \* @type: Seq(Str);
        S2 == <<"a", "b", "d">>
    IN
    LET P == UNION { Prefixes(seq) : seq \in { S1, S2 } } IN
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

TestIndexFirstSubSeq1 ==
    IndexFirstSubSeq(<<1, 2>>, <<1, 2, 3>>) = 1

TestIndexFirstSubSeq2 ==
    IndexFirstSubSeq(<<2, 3>>, <<1, 2, 3>>) = 2

TestIndexFirstSubSeq3 ==
    IndexFirstSubSeq(<<1, 2, 3>>, <<1, 2, 3>>) = 1

TestIndexFirstSubSeq4 ==
    IndexFirstSubSeq(<<3>>, <<1, 2, 3>>) = 3

TestReplaceFirstSubSeq1 ==
    ReplaceFirstSubSeq(intSeqEmpty, intSeqEmpty, intSeqEmpty) = intSeqEmpty

TestReplaceFirstSubSeq2 ==
    ReplaceFirstSubSeq(<<4>>, <<>>, <<>>) = <<4>>

TestReplaceFirstSubSeq3 ==
    ReplaceFirstSubSeq(<<4>>, <<4>>, <<>>) = <<>>

TestReplaceFirstSubSeq4 ==
    ReplaceFirstSubSeq(<<>>, <<>>, <<3, 2, 3, 4>>) = <<3, 2, 3, 4>>

TestReplaceFirstSubSeq5 ==
    ReplaceFirstSubSeq(<<4, 4>>, <<3, 2, 3, 4>>, <<3, 2, 3, 4>>) = <<4 ,4>>

TestReplaceFirstSubSeq6 ==
    ReplaceFirstSubSeq(<<4, 4>>, <<>>, <<3, 2, 3, 4>>) = <<4, 4, 3, 2, 3, 4>>

TestReplaceFirstSubSeq7 ==
    ReplaceFirstSubSeq(<<4, 4>>, <<4>>, <<3, 2, 3, 4>>) = <<3, 2, 3, 4, 4>>

TestReplaceFirstSubSeq8 ==
    ReplaceFirstSubSeq(<<>>, <<4>>, <<3, 2, 3, 4>>) = <<3, 2, 3>>

TestReplaceFirstSubSeq9 ==
    ReplaceFirstSubSeq(<<>>, <<4>>, <<3, 2, 3, 4, 4>>) = <<3, 2, 3, 4>>

TestReplaceFirstSubSeq10 ==
    ReplaceFirstSubSeq(<<4, 4>>, <<3>>, <<3, 2, 3, 4>>) = <<4, 4, 2, 3, 4>>

TestReplaceFirstSubSeq11 ==
    ReplaceFirstSubSeq(<<4>>, <<1, 2>>, <<1, 2, 1, 2>>) = <<4, 1, 2>>

TestReplaceFirstSubSeq12 ==
    ReplaceFirstSubSeq(<<4, 4>>, <<1, 2>>, <<1, 2, 1, 2>>) = <<4, 4, 1, 2>>

TestReplaceFirstSubSeq13 ==
    ReplaceFirstSubSeq(<<4, 4, 4>>, <<1, 2>>, <<1, 2, 1, 2>>)
        = <<4, 4, 4, 1, 2>>

TestReplaceFirstSubSeq14 ==
    ReplaceFirstSubSeq(<<1, 2>>, <<1, 2>>, <<1, 2, 2, 1>>) = <<1, 2, 2, 1>>

TestReplaceFirstSubSeq15 ==
    ReplaceFirstSubSeq(<<2, 1>>, <<1, 2>>, <<1, 2, 2, 1>>) = <<2, 1, 2, 1>>

(* WE DO NOT SUPPORT BoundedSeq
TestReplaceFirstSubSeq16 ==
    \A seq \in (BoundedSeq(1..5, 5) \ {<<>>}):
        /\ ReplaceFirstSubSeq(<<6>>, <<>>, seq) = <<6>> \o seq
        /\ ReplaceFirstSubSeq(<<6>>, <<Head(seq)>>, seq) = <<6>> \o Tail(seq)
 *)

TestReplaceFirstSubSeq18 ==
    ReplaceFirstSubSeq(<<"a">>, <<>>, <<>>) = <<"a">>

TestReplaceFirstSubSeq19 ==
    ReplaceFirstSubSeq(<<"a">>, <<"b">>, <<>>) = <<>>

TestReplaceFirstSubSeq20 ==
    ReplaceFirstSubSeq(<<"a">>, <<"d">>, <<"a", "b", "c">>) = <<"a", "b", "c">>

TestReplaceFirstSubSeq21 ==
    ReplaceFirstSubSeq(<<"d", "d", "d">>, <<"a", "b">>, <<"a", "b", "a", "b">>)
        = <<"d", "d", "d", "a", "b">>

TestReplaceFirstSubSeq22 ==
    ReplaceFirstSubSeq(<<"d", "d", "d">>, <<"a", "a">>, <<"a", "a", "a">>)
        = <<"d", "d", "d", "a">>

TestReplaceFirstSubSeq23 ==
    ReplaceFirstSubSeq(<<"d", "d", "d">>,
        <<"a", "b", "a", "b">>, <<"a", "b", "a", "b">>) = <<"d", "d", "d">>

\* this test is a disjunction of all smaller tests
AllTests ==
    /\ TestSetToSeq1
    /\ TestSetToSeq2
    /\ TestSetToSeq3
    /\ TestSetToSeq4
    /\ TestSetToSortSeq1
    /\ TestSetToSortSeq2
    /\ TestSetToSortSeq3
    /\ TestSetToSortSeq4
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
    /\ TestRemove1
    /\ TestRemove2
    /\ TestRemove3
    /\ TestRemove4
    /\ TestRemove5
    /\ TestRemove6
    /\ TestRemove7
    /\ TestReplaceAll1
    /\ TestReplaceAll2
    /\ TestInsertAt1
    /\ TestInsertAt2
    /\ TestInsertAt3
    /\ TestInsertAt4
    /\ TestReplaceAt1
    /\ TestReplaceAt2
    /\ TestRemoveAt1
    /\ TestRemoveAt2
    /\ TestRemoveAt3
    /\ TestRemoveAt4
    /\ TestCons1
    /\ TestFront1
    /\ TestLast1
    /\ TestIsPrefix1
    /\ TestIsPrefix2
    /\ TestIsPrefix3
    /\ TestIsPrefix4
    /\ TestIsPrefix5
    /\ TestIsPrefix6
    /\ TestIsPrefix7
    /\ TestIsPrefix8
    /\ TestIsPrefix9
    /\ TestIsPrefix10
    /\ TestIsPrefix11
    /\ TestIsPrefix12
    /\ TestIsPrefix13
    /\ TestIsStrictPrefix1
    /\ TestIsStrictPrefix2
    /\ TestIsStrictPrefix3
    /\ TestIsStrictPrefix4
    /\ TestIsStrictPrefix5
    /\ TestIsSuffix1
    /\ TestIsSuffix2
    /\ TestIsSuffix3
    /\ TestIsSuffix4
    /\ TestIsStrictSuffix1
    /\ TestPrefixes1
    /\ TestPrefixes2
    /\ TestPrefixes3
    /\ TestPrefixes4
    /\ TestPrefixes5
    /\ TestLongestCommonPrefix2
    /\ TestLongestCommonPrefix3
    /\ TestLongestCommonPrefix5
    /\ TestCommonPrefixes1
    /\ TestLongestCommonPrefix1
    /\ TestLongestCommonPrefix4
    /\ TestFoldSeq1
    /\ TestFoldLeft1
    /\ TestFoldRight1
    /\ TestFlattenSeq1
    /\ TestFlattenSeq2
    /\ TestFlattenSeq3
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
    /\ TestIndexFirstSubSeq1
    /\ TestIndexFirstSubSeq2
    /\ TestIndexFirstSubSeq3
    /\ TestIndexFirstSubSeq4
    /\ TestReplaceFirstSubSeq1
    /\ TestReplaceFirstSubSeq2
    /\ TestReplaceFirstSubSeq3
    /\ TestReplaceFirstSubSeq4
    /\ TestReplaceFirstSubSeq5
    /\ TestReplaceFirstSubSeq6
    /\ TestReplaceFirstSubSeq7
    /\ TestReplaceFirstSubSeq8
    /\ TestReplaceFirstSubSeq9
    /\ TestReplaceFirstSubSeq10
    /\ TestReplaceFirstSubSeq11
    /\ TestReplaceFirstSubSeq12
    /\ TestReplaceFirstSubSeq13
    /\ TestReplaceFirstSubSeq14
    /\ TestReplaceFirstSubSeq15
    /\ TestReplaceFirstSubSeq18
    /\ TestReplaceFirstSubSeq19
    /\ TestReplaceFirstSubSeq20
    /\ TestReplaceFirstSubSeq21
    /\ TestReplaceFirstSubSeq22
    /\ TestReplaceFirstSubSeq23

===============================================================================
