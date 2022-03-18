--------------------------- MODULE Bags -----------------------------------
(*****************************************************************************)
(* This is a standard module for use with the Apalache model checker.        *)
(* It reimplements the operators from the Bags.tla module, such that         *)
(* their definitions lie within the Apalache-supported fragment of TLA+.     *)
(*                                                                           *)
(* Jure Kukovec, 2021                                                        *)
(*****************************************************************************)

EXTENDS Apalache, Integers

(**
 * A bag is a function from `a` to Int, where `a` is the type of the bag contents
 * One can alias `typeAlias: A = a -> a`,
 * but (A, a) is NOT equivalent to (a -> a, a), but to `(b -> b, a)` instead.
 * Avoid using the alias until this is resolved.
 *
 * @typeAlias: BAG = a -> Int;
 *)
LOCAL ALIAS == TRUE

(**
 * True iff B is a bag.
 *
 * @type: (a -> Int) => Bool;
 *)
IsABag(B) ==
  \A x \in DOMAIN B: B[x] > 0

(**
 * The set of elements at least one copy of which is in B.
 *
 * @type: (a -> Int) => Set(a);
 *)
BagToSet(B) == DOMAIN B

(**
 * The bag that contains one copy of every element of the set S.
 *
 * @type: (Set(a)) => a -> Int;
 *)
SetToBag(S) == [e \in S |-> 1]

(**
 * The \in operator for bags.
 *
 * @type: (a, a -> Int) => Bool;
 *)
BagIn(e,B) == e \in BagToSet(B)

\* @type: () => a -> Int;
EmptyBag == [x \in {} |-> 0]

(**
 * The union of bags B1 and B2.
 *
 * @type: (a -> Int, a -> Int) => a -> Int;
 *)
B1 (+) B2  ==
    LET \* @type: Set(a);
        D1 == DOMAIN B1
        \* @type: Set(a);
        D2 == DOMAIN B2
    IN
    [e \in D1 \union D2 |->
        (IF e \in D1 THEN B1[e] ELSE 0) + (IF e \in D2 THEN B2[e] ELSE 0) ]

(**
 * The bag B1 with the elements of B2 removed--that is, with one copy
 * of an element removed from B1 for each copy of the same element in
 * B2. If B2 has at least as many copies of e as B1, then B1 (-) B2
 * has no copies of e.
 *
 * @type: (a -> Int, a -> Int) => a -> Int;
 *)
B1 (-) B2  ==
  (************************************************************************)
  (************************************************************************)
  LET \* @type: () => a -> Int;
    WithZeros == [e \in DOMAIN B1 |-> B1[e] - (IF e \in DOMAIN B2 THEN B2[e] ELSE 0)]
  IN
  LET \* @type: () => Set(a);
    NewDomain == {e \in DOMAIN WithZeros : WithZeros[e] > 0}
  IN
  [e \in NewDomain |-> WithZeros[e]]

(**
 * The bag union of all elements of the set S of bags.
 *
 * @type: (Set(a -> Int)) => a -> Int;
 *)
BagUnion(S) ==
  LET \* @type: (a -> Int,a -> Int) => a -> Int;
      PlusAsPrefix(B1,B2) == B1 (+) B2
  IN
  FoldSet( PlusAsPrefix, EmptyBag, S )

(**
 * The subset operator for bags.  B1 \sqsubseteq B2 iff, for all e, bag
 * B2 has at least as many copies of e as bag B1 does.
 *
 * @type: (a -> Int, a -> Int) => Bool;
 *)
B1 \sqsubseteq B2  ==
  /\ (DOMAIN B1) \subseteq (DOMAIN B2)
  /\ \A e \in DOMAIN B1 : B1[e] \leq B2[e]

(**
 * The set of all subbags of bag B.
 *
 * @type: (a -> Int) => Set(a -> Int);
 *)
SubBag(B) ==
    __NotSupportedByModelChecker("SubBag in Bags")

  (*******************  Here is the definition from the TLA+ book. ********
  LET AllBagsOfSubset ==
        UNION {[SB -> {n \in Nat : n > 0}] : SB \in SUBSET BagToSet(B)}
  IN  {SB \in AllBagsOfSubset : \A e \in DOMAIN SB : SB[e] \leq B[e]}
  ***************************************************************************)

(**
 * The bag analog of the set {F(x) : x \in B} for a set B. It's the bag
 * that contains, for each element e of B, one copy of F(e) for every
 * copy of e in B. This defines a bag iff, for any value v, the set of
 * e in B such that F(e) = v is finite.
 *
 * @type: ((a) => b, a -> Int) => b -> Int;
 *)
BagOfAll(F(_), B) ==
  LET \* @type: (b -> Int, a) => b -> Int;
      Extend(partialB,elem) == partialB (+) [e \in {F(elem)} |-> B[elem]]
  IN FoldSet( Extend, EmptyBag, DOMAIN B )

(**
 * If B is a finite bag (one such that BagToSet(B) is a finite set),
 * then this is its cardinality (the total number of copies of elements
 * in B).  Its value is unspecified if B is infinite.
 *
 * @type: (a -> Int) => Int;
 *)
BagCardinality(B) ==
  LET \* @type: (Int, a) => Int;
      CountElem(i, e) == i + B[e]
  IN
  FoldSet(CountElem, 0, DOMAIN B)

(**
 * If B is a bag, then CopiesIn(e, B) is the number of copies of e in
 * B. If ~BagIn(e, B), then CopiesIn(e, B) = 0.
 *
 * @type: (a, a -> Int) => Int;
 *)
CopiesIn(e, B) ==
  IF BagIn(e, B) THEN B[e] ELSE 0
=============================================================================
