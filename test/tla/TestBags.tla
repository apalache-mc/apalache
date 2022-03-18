---------- MODULE TestBags ----------

EXTENDS Integers, ApalacheBags

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

====================