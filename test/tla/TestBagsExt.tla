---------- MODULE TestBagsExt ----------

EXTENDS Integers, Apalache, Bags, BagsExt

TestBagAdd1 ==
    LET B == SetToBag({1, 2}) IN
    BagAdd(B, 2) = B (+) SetToBag({2})

TestBagAdd2 ==
    LET B == SetToBag({1, 2}) IN
    BagAdd(B, 3) = B (+) SetToBag({3})

TestBagRemove1 ==
    LET B == SetToBag({1, 2}) IN
    BagRemove(B, 2) = B (-) SetToBag({2})

TestBagRemove2 ==
    LET B == SetToBag({1, 2}) IN 
           /\ BagRemove(B, 3) = B (-) SetToBag({3})
           /\ BagRemove(B, 3) = B

TestBagRemoveAll1 ==
    LET B == SetAsFun({<<1, 2>>, <<2, 1>>}) IN
    BagRemoveAll(B, 1) = SetToBag({2})

Init == TRUE

Next == TRUE

AllTests ==
  /\ TestBagAdd1
  /\ TestBagAdd2
  /\ TestBagRemove1
  /\ TestBagRemove2
  /\ TestBagRemoveAll1

====================
