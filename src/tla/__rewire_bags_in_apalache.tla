--------------------------- MODULE Bags -----------------------------------
(*****************************************************************************)
(* This is a standard module for use with the Apalache model checker.        *)
(* It reimplements the operators from the Bags.tla module, such that         *)
(* their definitions lie within the Apalache-supported fragment of TLA+.     *)
(*                                                                           *)
(* Jure Kukovec, 2021                                                        *)
(*****************************************************************************)

EXTENDS Apalache, Integers

\* A bag is a function from `a` to Int, where `a` is the type of the bag contents
\*       One can alias `typeAlias: A = a -> a`,
\*       but (A, a) is NOT equivalent to (a -> a, a), but to `(b -> b, a)` instead.
\* Avoid using the alias until this is resolved.
\* @typeAlias: BAG = a -> Int;
LOCAL ALIAS == TRUE

\* @type: (a -> Int) => Bool;
IsABag(B) ==
  (************************************************************************)
  (* True iff B is a bag.                                                 *)
  (************************************************************************)
  \A x \in DOMAIN B: B[x] > 0

\* @type: (a -> Int) => Set(a);
BagToSet(B) == DOMAIN B
  (************************************************************************)
  (* The set of elements at least one copy of which is in B.              *)
  (************************************************************************)

\* @type: (Set(a)) => a -> Int;
SetToBag(S) == [e \in S |-> 1]
  (************************************************************************)
  (* The bag that contains one copy of every element of the set S.        *)
  (************************************************************************)

\* @type: (a, a -> Int) => Bool;
BagIn(e,B) == e \in BagToSet(B)
  (************************************************************************)
  (* The \in operator for bags.                                           *)
  (************************************************************************)

\* @type: () => a -> Int;
EmptyBag == [x \in {} |-> 0]

\* @type: (a -> Int, a -> Int) => a -> Int;
B1 (+) B2  ==
  (************************************************************************)
  (* The union of bags B1 and B2.                                         *)
  (************************************************************************)
    LET \* @type: Set(a);
        D1 == DOMAIN B1
        \* @type: Set(a);
        D2 == DOMAIN B2
    IN [e \in D1 \union D2 |->
      (IF e \in D1 THEN B1[e] ELSE 0)
    + (IF e \in D2 THEN B2[e] ELSE 0) ]

\* @type: (a -> Int, a -> Int) => a -> Int;
B1 (-) B2  ==
  (************************************************************************)
  (* The bag B1 with the elements of B2 removed--that is, with one copy   *)
  (* of an element removed from B1 for each copy of the same element in   *)
  (* B2.  If B2 has at least as many copies of e as B1, then B1 (-) B2    *)
  (* has no copies of e.                                                  *)
  (************************************************************************)
  LET
    \* @type: () => a -> Int;
    WithZeros == [e \in DOMAIN B1 |-> B1[e] - (IF e \in DOMAIN B2 THEN B2[e] ELSE 0)]
  IN LET
    \* @type: () => Set(a);
    NewDomain == {e \in DOMAIN WithZeros : WithZeros[e] > 0}
  IN [e \in NewDomain |-> WithZeros[e]]

\* @type: (Set(a -> Int)) => a -> Int;
BagUnion(S) ==
  (************************************************************************)
  (* The bag union of all elements of the set S of bags.                  *)
  (************************************************************************)
  LET
    \* @type: (a -> Int,a -> Int) => a -> Int;
    PlusAsPrefix(B1,B2) == B1 (+) B2
  IN FoldSet( PlusAsPrefix, EmptyBag, S )

\* @type: (a -> Int, a -> Int) => Bool;
B1 \sqsubseteq B2  ==
  (************************************************************************)
  (* The subset operator for bags.  B1 \sqsubseteq B2 iff, for all e, bag *)
  (* B2 has at least as many copies of e as bag B1 does.                  *)
  (************************************************************************)
  /\ (DOMAIN B1) \subseteq (DOMAIN B2)
  /\ \A e \in DOMAIN B1 : B1[e] \leq B2[e]

\* TODO: Introduce Unsupported("...")
\* @type: (a -> Int) => Set(a -> Int);
SubBag(B) == {}
  (************************************************************************)
  (* The set of all subbags of bag B.                                     *)
  (************************************************************************)
  \* LET
  \*   \* &type: Set(a);
  \*   DOM == DOMAIN B
  \* IN LET
  \*   \* &type: (Int,Int) => Int;
  \*   Max(a,b) == IF a > b THEN a ELSE b
  \* IN LET
  \*   \* &type: () => Int;
  \*   MaxCount == FoldSet( Max, 0, { B[x]: x \in DOM } )
  \* IN LET
  \*   \* &type: () => Set(a -> Int);
  \*   ResultWithZeros == { bag \in [ DOM -> 0..MaxCount ]: \A e \in DOM: bag[e] <= B[e] }
  \* IN LET
  \*   \* &type: (a -> Int) => a -> Int;
  \*   RmZeroes(bag) == [x \in {e \in DOM: bag[e] > 0} |-> bag[x]]
  \* IN
  \*   { RmZeroes(b) : b \in ResultWithZeros }

  \* LET \* &type: (a, Int) => Set(a -> Int);
  \*     AllSingleElemBags(elem, max) == { [e \in {elem} |-> k]: k \in 1..max }
  \* IN LET \* &type: (Set(a -> Int), a -> Int) => Set(a -> Int);
  \*     AddToAll( T, elem ) == { t (+) elem : t \in T }
  \* IN LET \* &type: (Set(a -> Int), a) => Set(a -> Int);
  \*     AddAllQuantitiesOfElem( partial, elem ) == FoldSet( AddToAll, {EmptyBag}, AllSingleElemBags(elem, B[elem]) )
  \* IN LET \* &type: (Set(a)) => Set(a -> Int);
  \*     AllBagsWithDomain(D) == FoldSet( AddAllQuantitiesOfElem, {EmptyBag}, D )
  \* IN UNION { AllBagsWithDomain(D) : D \in SUBSET (DOMAIN B) }

  (*******************  Here is the definition from the TLA+ book. ********
  LET AllBagsOfSubset ==
        UNION {[SB -> {n \in Nat : n > 0}] : SB \in SUBSET BagToSet(B)}
  IN  {SB \in AllBagsOfSubset : \A e \in DOMAIN SB : SB[e] \leq B[e]}
  ***************************************************************************)

\* @type: ((a) => b, a -> Int) => b -> Int;
BagOfAll(F(_), B) ==
  (************************************************************************)
  (* The bag analog of the set {F(x) : x \in B} for a set B. It's the bag *)
  (* that contains, for each element e of B, one copy of F(e) for every   *)
  (* copy of e in B. This defines a bag iff, for any value v, the set of  *)
  (* e in B such that F(e) = v is finite.                                 *)
  (************************************************************************)
  LET \* @type: (b -> Int, a) => b -> Int;
      Extend(partialB,elem) == partialB (+) [e \in {F(elem)} |-> B[elem]]
  IN FoldSet( Extend, EmptyBag, DOMAIN B )

\* @type: (a -> Int) => Int;
BagCardinality(B) ==
  (************************************************************************)
  (* If B is a finite bag (one such that BagToSet(B) is a finite set),    *)
  (* then this is its cardinality (the total number of copies of elements *)
  (* in B).  Its value is unspecified if B is infinite.                   *)
  (************************************************************************)
  LET \* @type: (Int, a) => Int;
      CountElem(i, e) == i + B[e]
  IN FoldSet(CountElem, 0, DOMAIN B)

\* @type: (a, a -> Int) => Int;
CopiesIn(e, B) ==
  (************************************************************************)
  (* If B is a bag, then CopiesIn(e, B) is the number of copies of e in   *)
  (* B. If ~BagIn(e, B), then CopiesIn(e, B) = 0.                         *)
  (************************************************************************)
  IF BagIn(e, B) THEN B[e] ELSE 0
=============================================================================
