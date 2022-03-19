---------- MODULE TestBags ----------

EXTENDS Integers, Bags

\* @type: (a, Int) => a -> Int;
SingleElemBag(x, N) == [e \in {x} |-> N]

TestIsABag ==
  LET
    RealBag == SingleElemBag(1,1)
    FakeBag == SingleElemBag(1,-1)
  IN
    /\ IsABag(RealBag)
    /\ ~IsABag(FakeBag)

TestBagToSet ==
  /\ BagToSet(SingleElemBag(1,1)) = {1}
  /\ BagToSet(SingleElemBag("a", 1)) = {"a"}

TestSetToBag ==
  LET
    S1 == 1..3
    S2 == {"a", "b"}
  IN
    /\ LET B == SetToBag(S1) IN
      \A x \in S1:
        /\ x \in DOMAIN B
        /\ B[x] = 1
    /\ LET B == SetToBag(S2) IN
      \A x \in S2:
        /\ x \in DOMAIN B
        /\ B[x] = 1

TestBagIn ==
  LET
    S1 == 1..3
    S2 == {"a","b"}
  IN
    /\ LET B == SetToBag(S1) IN
      \A x \in S1:
        BagIn(x, B)
    /\ LET B == SetToBag(S2) IN
      \A x \in S2:
        BagIn(x, B)

TestEmptyBag ==
  LET
    \* @type: () => Str -> Int;
    Bstr == EmptyBag
    \* @type: () => Int -> Int;
    Bint == EmptyBag
  IN
    /\ ~BagIn(1, Bint)
    /\ ~BagIn("a", Bstr)

TestPlus ==
  LET
    A1 == SingleElemBag(1, 1)
    A2 == SingleElemBag(1, 3)
    B1 == SingleElemBag("a", 1)
    B2 == SingleElemBag("b", 2)
  IN LET
    A1A2 == A1 (+) A2
    A2A1 == A2 (+) A1
    B1B2 == B1 (+) B2
    B2B1 == B2 (+) B1
  IN
    /\ A1A2 = A2A1
    /\ A1A2 = SingleElemBag(1, 4)
    /\ B1B2 = B2B1
    /\ BagToSet(B1B2) = {"a","b"}
    /\ B1B2["a"] = B1["a"]
    /\ B1B2["b"] = B2["b"]

TestMinus ==
  LET
    A1 == SingleElemBag(1, 1)
    A2 == SingleElemBag(1, 3)
    B1 == SingleElemBag("a", 1)
    B2 == SingleElemBag("b", 2)
  IN LET
    A1A2 == A1 (-) A2
    A2A1 == A2 (-) A1
    B1B2 == B1 (-) B2
    B2B1 == B2 (-) B1
  IN
    /\ A1A2 = EmptyBag
    /\ A2A1 = SingleElemBag(1, 2)
    /\ B1B2 = B1
    /\ B2B1 = B2

TestBagUnion ==
  LET
    A1 == SingleElemBag(1, 1)
    A2 == SingleElemBag(1, 2)
    A3 == SingleElemBag(1, 3)
    B1 == SingleElemBag("a", 1)
    B2 == SingleElemBag("a", 2)
    B3 == SingleElemBag("c", 3)
  IN LET
    AU == BagUnion({A1,A2,A3})
    BU == BagUnion({B1,B2,B3})
  IN
    /\ AU = SingleElemBag(1, 6)
    /\ BagToSet(BU) = {"a","c"}
    /\ BU["a"] = 3

TestSqsubseteq ==
  LET 
    A1 == SingleElemBag(1, 1)
    A2 == SingleElemBag(1, 2)
    B1 == SingleElemBag("a", 1)
    B2 == SingleElemBag("c", 3)
  IN LET
    A1A2 == A1 \sqsubseteq A2
    A2A1 == A2 \sqsubseteq A1
    B1B2 == B1 \sqsubseteq B2
    B2B1 == B2 \sqsubseteq B1
  IN
    /\ A1A2 
    /\ ~A2A1
    /\ ~B1B2
    /\ ~B2B1

\* Disabled, because SubBag is not supported
TestSubBag == TRUE

TestBagOfAll ==
  LET
    \* injective
    \* @type: (a) => <<a,a>>;
    F1(x) == <<x,x>>
    \* non-injective
    \* @type: (a) => Int;
    F2(x) == 1
  IN LET
    A1 == SingleElemBag(1, 1) (+) SingleElemBag(2, 2)
    A2 == SingleElemBag("a", 1) (+) SingleElemBag("c", 3)
  IN LET 
    A1F1 == BagOfAll(F1, A1)
    A1F2 == BagOfAll(F2, A1)
    A2F1 == BagOfAll(F1, A2)
    A2F2 == BagOfAll(F2, A2)
  IN
    /\ DOMAIN A1F1 = {<<1,1>>, <<2,2>>}
    /\ A1F1[1,1] = 1
    /\ A1F1[2,2] = 2
    /\ A1F2 = SingleElemBag(1,3)
    /\ DOMAIN A2F1 = {<<"a","a">>, <<"c","c">>}
    /\ A2F1["a","a"] = 1
    /\ A2F1["c","c"] = 3
    /\ A2F2 = SingleElemBag(1,4)

TestBagCardinality ==
  LET
    A1 == SingleElemBag(1, 1)
    A2 == SingleElemBag(1, 3)
    B1 == SingleElemBag("a", 1)
    B2 == SingleElemBag("b", 2)
    \* @type: Int -> Int;
    EB == EmptyBag
  IN LET
    CA1 == BagCardinality(A1)
    CA2 == BagCardinality(A2)
    CB1 == BagCardinality(B1)
    CB2 == BagCardinality(B2)
  IN
    /\ CA1 = 1
    /\ CA2 = 3
    /\ CB1 = 1
    /\ CB2 = 2
    /\ BagCardinality(EB) = 0
    /\ BagCardinality(A1 (+) A1) = 2 * CA1
    /\ BagCardinality(A1 (+) A2) = CA1 + CA2
    /\ BagCardinality(B2 (-) B1) = CB2 \* B2 - B1 = B2

TestCopiesIn ==
  LET
    A == SingleElemBag(1, 1) (+) SingleElemBag(1, 3)
    B == SingleElemBag("a", 1) (+) SingleElemBag("b", 2)
    \* @type: Str -> Int;
    EB == EmptyBag
  IN 
    /\ CopiesIn(1, A) = 4
    /\ CopiesIn(2, A) = 0
    /\ CopiesIn("a", B) = 1
    /\ CopiesIn("b", B) = 2
    /\ CopiesIn("c", B) = 0
    /\ CopiesIn("a", EB) = 0
    /\ CopiesIn("b", EB) = 0

Init == TRUE

Next == TRUE

Inv ==
  /\ TestIsABag
  /\ TestBagToSet
  /\ TestSetToBag
  /\ TestBagIn
  /\ TestEmptyBag
  /\ TestPlus
  /\ TestMinus
  /\ TestBagUnion
  /\ TestSqsubseteq
  /\ TestSubBag
  /\ TestBagOfAll
  /\ TestBagCardinality
  /\ TestCopiesIn

====================