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
BagAdd(B, x) ==
   IF x \in DOMAIN B
   THEN [e \in DOMAIN B |-> IF e = x THEN B[e] + 1 ELSE B[e]]
   ELSE [e \in DOMAIN B \union { x } |-> IF e = x THEN 1 ELSE B[e]]

(**
 * Remove an element x from bag B. Same as B (-) SetToBag({x}).
 *
 * @type: (a -> Int, a) => (a -> Int);
 *)
BagRemove(B, x) ==
   IF x \in DOMAIN B
   THEN IF B[x] = 1
        THEN [e \in DOMAIN B \ {x} |-> B[e]]
        ELSE [e \in DOMAIN B |-> IF e = x THEN B[e] - 1 ELSE B[e]]
   ELSE B

(**
 * Remove all copies of an element x from bag B.
 *
 * @type: (a -> Int, a) => (a -> Int);
 *)
BagRemoveAll(B, x) ==
   [e \in DOMAIN B \ {x} |-> B[e]]

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
MapThenFoldBag(op(_, _), base, f(_), choose(_), B) ==
    __NotSupportedByModelChecker("MapThenFoldBag. Use FoldFunction.")

(**
 * Fold op over all elements of bag B, starting with value base.
 *
 * Apalache does not support this operator. Use FoldFunction.
 *
 * @type: ((a, b) => b, b, a -> Int) => (a -> Int);
 *)
FoldBag(op(_, _), base, B) ==
    __NotSupportedByModelChecker("FoldBag. Use FoldFunction.")

(**
 * Compute the sum of the elements of B.
 *
 * @type: (Int -> Int) => Int;
 *)
SumBag(B) ==
  LET __map(x, y) == x + y * B[y] IN
  __ApalacheFoldSet(__map, 0, DOMAIN B)

(**
 * Compute the product of the elements of B.
 *
 * @type: (Int -> Int) => Int;
 *)
ProductBag(B) ==
  LET __map(x, y) == x * (y^B[y]) IN
  __ApalacheFoldSet(__map, 1, DOMAIN B)

=============================================================================
