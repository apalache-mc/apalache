------------------------ MODULE FiniteSetsExt ---------------------------------
\*------ MODULE __rewire_finite_sets_ext_in_apalache -----------------------
(**
 * ^^^^^^^^^^^^^^^^^^^^^^ We have to call this module FiniteSetsExt in any
 * case, otherwise, SANY complains.
 *
 * This file contains alternative definitions for the operators defined in
 * FiniteSetsExt. Most importantly, we are adding type annotations. We also
 * define the Apalache-compatible behavior.
 *
 * These definitions are automatically rewired by the Apalache importer.
 *
 * Compare with the original definitions in FiniteSetsExt.tla:
 *
 * https://github.com/tlaplus/CommunityModules/blob/master/modules/FiniteSetsExt.tla
 *)

LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE __apalache_folds 
LOCAL INSTANCE Functions

(**
 * Fold op over the elements of set using base as starting value.
 * Note that this FoldSet is different from Apalache!ApaFoldSet.
 *
 * Example:
 *         FoldSet(LAMBA x,y : x + y, 0, 0 .. 10) = 55
 *
 * @type: ((a, b) => b, b, Set(a)) => b;
 *)
FoldSet(__op(_, _), __base, __set) ==
    \* ApalacheFoldSet accumulates the result in the left argument,
    \* whereas FiniteSetsExt!FoldSet accumulates the result
    \* in the right argument.
    LET __OpSwap(__x, __y) == __op(__y, __x) IN
    __ApalacheFoldSet(__OpSwap, __base, __set)

(**
 * Calculate the sum of the elements in set.
 *
 * Example: Sum(0 .. 10) = 55
 *
 * @type: Set(Int) => Int;
 *)
SumSet(__set) ==
   LET __Plus(__x, __y) == __x + __y IN
   __ApalacheFoldSet(__Plus, 0, __set)

(**
 * Calculate the product of the elements in set.
 *
 * Example: Product(1 .. 3) = 6
 *
 * @type: Set(Int) => Int;
 *)
ProductSet(__set) ==
   LET __Mult(__x, __y) == __x * __y IN
   __ApalacheFoldSet(__Mult, 1, __set)

(**
 * An alias for FoldSet. ReduceSet was used instead of FoldSet in
 * earlier versions of the community modules.
 *
 * @type: ((a, b) => b, Set(a), b) => b;
 *)
ReduceSet(__op(_, _), __set, __acc) == 
   FoldSet(__op, __acc, __set)

(**
 * Starting from base, apply op to f(x), for all x \in S, in an arbitrary
 * order. It is assumed that op is associative and commutative.
 *
 * Example: FlattenSet({{1},{2}}) = {1,2}
 *
 * @type: Set(Set(a)) => Set(a);
 *)
FlattenSet(__S) ==
  UNION __S

(**
 * The symmetric difference of two sets.
 *
 * The symmetric difference of sets A and B is the set containing all
 * elements that are present in either A or B but not in their intersection.
 *
 * @type: (Set(a), Set(a)) => Set(a);
 *)
SymDiff(__A, __B) ==
    { __x \in __A \union __B: __x \notin __A \/ __x \notin __B}

(**
 * Quantify the elements in S matching the predicate (LAMDBA) P.
 *
 * This operator is overridden by FiniteSetsExt#quantify whose
 * implementation does *not* enumerate the intermediate set! This is
 * the only advantage that Quantify(...) has over Cardinality(...).
 *
 * Example: Quantify(1..9, LAMBDA n : n % 2 = 0) = 4
 *
 * @type: (Set(a), (a => Bool)) => Int;
 *)
Quantify(__S, __P(_)) ==
    LET __CondCount(__n, __e) ==
        __n + IF __P(__e) THEN 1 ELSE 0
    IN
    __ApalacheFoldSet(__CondCount, 0, __S)


(**
 * A k-subset ks of a set S has Cardinality(ks) = k.  The number of
 * k-subsets of a set S with Cardinality(S) = n is given by the binomial
 * coefficients n over k.  A set S with Cardinality(S) = n has 2^n
 * k-subsets.  \A k \notin 0..Cardinality(S): kSubset(k, S) = {}.
 *
 * This operator is overridden by FiniteSetsExt#kSubset whose
 * implementation, contrary to  { s \in SUBSET S : Cardinality(s) = k },
 * only enumerates the k-subsets of S and not all subsets.
 *
 * Example: kSubset(2, 1..3) = {{1,2},{2,3},{3,1}}
 *
 * @type: (Int, Set(a)) => Set(Set(a));
 *)
kSubset(__k, __S) == 
   { __s \in SUBSET __S : Cardinality(__s) = __k }

(**
 * We define Max(S) and Min(S) to be the maximum and minimum,
 * respectively, of a finite, non-empty set S of integers.
 *
 * @type: Set(Int) => Int;
 *)
Max(__S) == CHOOSE __x \in __S : \A __y \in __S : __x >= __y

(**
 * @type: Set(Int) => Int;
 *)
Min(__S) == CHOOSE __x \in __S : \A __y \in __S : __x =< __y

(**
 * Compute all sets that contain one element from each of the input sets:
 *
 * Example:
 *          Choices({{1,2}, {2,3}, {5}}) =
 *                         {{2, 5}, {1, 2, 5}, {1, 3, 5}, {2, 3, 5}}
 *
 * @type: Set(Set(a)) => Set(Set(a));
 *)
Choices(__Sets) == 
  LET __ChoiceFunction(__Ts) == 
    { __f \in [__Ts -> UNION __Ts] : \A __T \in __Ts : __f[__T] \in __T }
  IN  { Range(__f) : __f \in __ChoiceFunction(__Sets) }

(**
 * Choose a unique element from the input set matching the predicate
 * (LAMDBA) P.
 *
 * Contrary to CHOOSE, fails with
 *      CHOOSE x \\in S: P, but no element of S satisfies P:
 * not just if P(_) holds for none of the elements in S, but also if
 * P(_) holds for more than one element in S.
 *
 * Example: ChooseUnique({2, 3, 4, 5}, LAMBDA x : x % 3 = 1) = 4
 *
 * @type: (Set(a), (a => Bool)) => a;
 *)
ChooseUnique(__S, __P(_)) == 
  CHOOSE __x \in __S :
    __P(__x) /\ \A __y \in __S : __P(__y) => __y = __x
===============================================================================
