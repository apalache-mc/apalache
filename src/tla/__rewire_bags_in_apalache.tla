--------------------------- MODULE Bags -----------------------------------
(*****************************************************************************)
(* This is a standard module for use with the Apalache model checker.        *)
(* It reimplements the operators from the Bags.tla module, such that         *)
(* their definitions lie within the Apalache-supported fragment of TLA+.     *)
(*                                                                           *)
(* Jure Kukovec, 2021                                                        *)
(*****************************************************************************)

EXTENDS Integers, __apalache_internal, __apalache_folds

(**
 * A bag is a function from `a` to Int, where `a` is the type of the bag contents
 * One can alias `typeAlias: A = a -> a`,
 * but (A, a) is NOT equivalent to (a -> a, a), but to `(b -> b, a)` instead.
 * Avoid using the alias until this is resolved.
 *
 * @typeAlias: BAG = a -> Int;
 *)
LOCAL __ALIAS == TRUE

(**
 * True iff B is a bag.
 *
 * @type: (a -> Int) => Bool;
 *)
IsABag(__B) ==
  \A __x \in DOMAIN __B: __B[__x] > 0

(**
 * The set of elements at least one copy of which is in B.
 *
 * @type: (a -> Int) => Set(a);
 *)
BagToSet(__B) == DOMAIN __B

(**
 * The bag that contains one copy of every element of the set S.
 *
 * @type: (Set(a)) => a -> Int;
 *)
SetToBag(__S) == [__e \in __S |-> 1]

(**
 * The \in operator for bags.
 *
 * @type: (a, a -> Int) => Bool;
 *)
BagIn(__e,__B) == __e \in BagToSet(__B)

\* @type: () => a -> Int;
EmptyBag == [__x \in {} |-> 0]

(**
 * The union of bags B1 and B2.
 *
 * @type: (a -> Int, a -> Int) => a -> Int;
 *)
__B1 (+) __B2  ==
    LET \* @type: Set(a);
        __D1 == DOMAIN __B1
        \* @type: Set(a);
        __D2 == DOMAIN __B2
    IN
    [ __e \in __D1 \union __D2 |->
        (IF __e \in __D1 THEN __B1[__e] ELSE 0) + 
        (IF __e \in __D2 THEN __B2[__e] ELSE 0) 
    ]

(**
 * The bag B1 with the elements of B2 removed--that is, with one copy
 * of an element removed from B1 for each copy of the same element in
 * B2. If B2 has at least as many copies of e as B1, then B1 (-) B2
 * has no copies of e.
 *
 * @type: (a -> Int, a -> Int) => a -> Int;
 *)
__B1 (-) __B2  ==
  (************************************************************************)
  (************************************************************************)
  LET \* @type: () => a -> Int;
    __WithZeros == 
      [ __e \in DOMAIN __B1 |-> __B1[__e] - 
        (IF __e \in DOMAIN __B2 THEN __B2[__e] ELSE 0)
      ]
  IN
  LET \* @type: () => Set(a);
    __NewDomain == {__e \in DOMAIN __WithZeros : __WithZeros[__e] > 0}
  IN
  [__e \in __NewDomain |-> __WithZeros[__e]]

(**
 * The bag union of all elements of the set S of bags.
 *
 * @type: (Set(a -> Int)) => a -> Int;
 *)
BagUnion(__S) ==
  LET \* @type: (a -> Int,a -> Int) => a -> Int;
      __PlusAsPrefix(__B1,__B2) == __B1 (+) __B2
  IN
  __ApalacheFoldSet( __PlusAsPrefix, EmptyBag, __S )

(**
 * The subset operator for bags.  B1 \sqsubseteq B2 iff, for all e, bag
 * B2 has at least as many copies of e as bag B1 does.
 *
 * @type: (a -> Int, a -> Int) => Bool;
 *)
__B1 \sqsubseteq __B2  ==
  /\ (DOMAIN __B1) \subseteq (DOMAIN __B2)
  /\ \A __e \in DOMAIN __B1 : __B1[__e] \leq __B2[__e]

(**
 * The set of all subbags of bag B.
 *
 * @type: (a -> Int) => Set(a -> Int);
 *)
SubBag(__B) ==
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
BagOfAll(__F(_), __B) ==
  LET \* @type: (b -> Int, a) => b -> Int;
      __Extend(__partialB,__elem) == 
        __partialB (+) [__e \in {__F(__elem)} |-> __B[__elem]]
  IN __ApalacheFoldSet( __Extend, EmptyBag, DOMAIN __B )

(**
 * If B is a finite bag (one such that BagToSet(B) is a finite set),
 * then this is its cardinality (the total number of copies of elements
 * in B).  Its value is unspecified if B is infinite.
 *
 * @type: (a -> Int) => Int;
 *)
BagCardinality(__B) ==
  LET \* @type: (Int, a) => Int;
      __CountElem(__i, __e) == __i + __B[__e]
  IN
  __ApalacheFoldSet(__CountElem, 0, DOMAIN __B)

(**
 * If B is a bag, then CopiesIn(e, B) is the number of copies of e in
 * B. If ~BagIn(e, B), then CopiesIn(e, B) = 0.
 *
 * @type: (a, a -> Int) => Int;
 *)
CopiesIn(__e, __B) ==
  IF BagIn(__e, __B) THEN __B[__e] ELSE 0
=============================================================================
