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
 * Note that this FoldSet is different from Apalache!FoldSet.
 *
 * Example:
 *         FoldSet(LAMBA x,y : x + y, 0, 0 .. 10) = 55
 *
 * @type: ((a, b) => b, b, Set(a)) => b;
 *)
FoldSet(op(_, _), base, set) ==
    \* ApalacheFoldSet is accumulating the result in the left argument,
    \* whereas FinitSetsExt!FoldSet is accumulating the result
    \* in the right argument.
    LET OpSwap(x, y) == op(y, x) IN
    __ApalacheFoldSet(OpSwap, base, set)

(**
 * Calculate the sum of the elements in set.
 *
 * Example: Sum(0 .. 10) = 55
 *
 * @type: Set(Int) => Int;
 *)
SumSet(set) ==
   LET Plus(x, y) == x + y IN
   __ApalacheFoldSet(Plus, 0, set)

(**
 * Calculuate the product of the elements in set.
 *
 * Example: Product(1 .. 3) = 6
 *
 * @type: Set(Int) => Int;
 *)
ProductSet(set) ==
   LET Mult(x, y) == x * y IN
   __ApalacheFoldSet(Mult, 1, set)

(**
 * An alias for FoldSet. ReduceSet was used instead of FoldSet in
 * earlier versions of the community modules.
 *
 * @type: ((a, b) => b, Set(a), b) => b;
 *)
ReduceSet(op(_, _), set, acc) == 
   FoldSet(op, set, acc)

(**
 * Starting from base, apply op to f(x), for all x \in S, in an arbitrary
 * order. It is assumed that op is associative and commutative.
 *
 * Example: FlattenSet({{1},{2}}) = {1,2}
 *
 * @type: Set(Set(a)) => Set(a);
 *)
FlattenSet(S) ==
  UNION S

(**
 * The symmetric difference of two sets.
 *
 * The symmetric difference of sets A and B is the set containing all
 * elements that are present in either A or B but not in their intersection.
 *
 * @type: (Set(a), Set(a)) => Set(a);
 *)
SymDiff(A, B) ==
    { x \in A \union B: x \notin A \/ x \notin B}

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
Quantify(S, P(_)) ==
    LET CondCount(n, e) ==
        n + IF P(e) THEN 1 ELSE 0
    IN
    __ApalacheFoldSet(CondCount, 0, S)


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
kSubset(k, S) == 
   { s \in SUBSET S : Cardinality(s) = k }

(**
 * We define Max(S) and Min(S) to be the maximum and minimum,
 * respectively, of a finite, non-empty set S of integers.
 *
 * @type: Set(Int) => Int;
 *)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

(**
 * @type: Set(Int) => Int;
 *)
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

(**
 * Compute all sets that contain one element from each of the input sets:
 *
 * Example:
 *          Choices({{1,2}, {2,3}, {5}}) =
 *                         {{2, 5}, {1, 2, 5}, {1, 3, 5}, {2, 3, 5}}
 *
 * @type: Set(Set(a)) => Set(Set(a));
 *)
Choices(Sets) == LET ChoiceFunction(Ts) == { f \in [Ts -> UNION Ts] : 
                                               \A T \in Ts : f[T] \in T }
                 IN  { Range(f) : f \in ChoiceFunction(Sets) }

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
ChooseUnique(S, P(_)) == CHOOSE x \in S :
                              P(x) /\ \A y \in S : P(y) => y = x
===============================================================================
