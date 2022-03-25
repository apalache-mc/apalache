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
=============================================================================
