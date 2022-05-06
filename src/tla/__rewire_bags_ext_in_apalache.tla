--------------------------- MODULE BagsExt -----------------------------------
\*------ MODULE __rewire_bags_ext_in_apalache -----------------------
(**
 * ^^^^^^^^^^^^^^^^^^^^^^ We have to call this module BagsExt in any
 * case, otherwise, SANY complains.
 *
 * This file contains alternative definitions for the operators defined in
 * BagsExt. Most importantly, we are adding type annotations. We also
 * define the Apalache-compatible behavior.
 *
 * These definitions are automatically rewired by the Apalache importer.
 *
 * Compare with the original definitions in BagsExt.tla:
 *
 * https://github.com/tlaplus/CommunityModules/blob/master/modules/BagsExt.tla
 *)

EXTENDS Integers, Bags, __apalache_internal, __apalache_folds

(**
 * Add an element x to bag B. Same as B (+) SetToBag({x}).
 *
 * @type: (a -> Int, a) => (a -> Int);
 *)
BagAdd(__B, __x) ==
   IF __x \in DOMAIN __B
   THEN [__e \in DOMAIN __B |-> IF __e = __x THEN __B[__e] + 1 ELSE __B[__e]]
   ELSE [__e \in DOMAIN __B \union { __x } |-> IF __e = __x THEN 1 ELSE __B[__e]]

(**
 * Remove an element x from bag B. Same as B (-) SetToBag({x}).
 *
 * @type: (a -> Int, a) => (a -> Int);
 *)
BagRemove(__B, __x) ==
   IF __x \in DOMAIN __B
   THEN IF __B[__x] = 1
        THEN [__e \in DOMAIN __B \ {__x} |-> __B[__e]]
        ELSE [__e \in DOMAIN __B |-> IF __e = __x THEN __B[__e] - 1 ELSE __B[__e]]
   ELSE __B

(**
 * Remove all copies of an element x from bag B.
 *
 * @type: (a -> Int, a) => (a -> Int);
 *)
BagRemoveAll(__B, __x) ==
   [__e \in DOMAIN __B \ {__x} |-> __B[__e]]

(**
 * Fold operation op over the images through f of all elements of bag
 * B, starting from base. The parameter choose indicates the order in
 * which elements of the bag are processed; all replicas of an element
 * are processed consecutively.
 *
 * Apalache does not support this operator. Use FoldFunction.
 *
 * @type: ((a, b) => b, b, a => b, Set(a) => a, a -> Int) => b;
 *)
MapThenFoldBag(__op(_, _), __base, __f(_), __choose(_), __B) ==
    __NotSupportedByModelChecker("MapThenFoldBag. Use FoldFunction.")

(**
 * Fold op over all elements of bag B, starting with value base.
 *
 * Apalache does not support this operator. Use FoldFunction.
 *
 * @type: ((a, b) => b, b, a -> Int) => (a -> Int);
 *)
FoldBag(__op(_, _), __base, __B) ==
    __NotSupportedByModelChecker("FoldBag. Use FoldFunction.")

(**
 * Compute the sum of the elements of B.
 *
 * @type: (Int -> Int) => Int;
 *)
SumBag(__B) ==
  LET __map(__x, __y) == __x + __y * __B[__y] IN
  __ApalacheFoldSet(__map, 0, DOMAIN __B)

(**
 * Compute the product of the elements of B.
 *
 * @type: (Int -> Int) => Int;
 *)
ProductBag(__B) ==
  LET __map(__x, __y) == __x * (__y^__B[__y]) IN
  __ApalacheFoldSet(__map, 1, DOMAIN __B)

=============================================================================
