--------------------------- MODULE Folds -----------------------------------
\*------ MODULE __rewire_folds_in_apalache -----------------------
(**
 * ^^^^^^^^^^^^^^^^^^^^^^ We have to call this module Folds in any
 * case, otherwise, SANY complains.
 *
 * This file contains alternative definitions for the operators defined in
 * Folds. Most importantly, we are adding type annotations. We also
 * define the Apalache-compatible behavior.
 *
 * These definitions are automatically rewired by the Apalache importer.
 *
 * Compare with the original definitions in Folds.tla:
 *
 * https://github.com/tlaplus/CommunityModules/blob/master/modules/Folds.tla
 *)

EXTENDS __apalache_internal


(**
 * Starting from base, apply op to f(x), for all x \in S, by choosing the set
 * elements with `choose`. If there are multiple ways for choosing an element,
 * op should be associative and commutative. Otherwise, the result may depend
 * on the concrete implementation of `choose`.
 *
 * FoldSet, a simpler version for sets is contained in FiniteSetsEx.
 * FoldFunction, a simpler version for functions is contained in Functions.
 * FoldSeq, a simpler version for sequences is contained in SequencesExt.
 *
 * Apalache (the model checker) does not support MapThenFoldSet.
 * However, we introduce this definition for the type checker.
 *
 * @type: ((a, b) => b, b, c => a, Set(c) => c, Set(c)) => b;
 *)
MapThenFoldSet(__op(_, _), __base, __f(_), __choose(_), __S) ==
  __NotSupportedByModelChecker("MapThenFoldSet. Use FoldSet, FoldSeq, FoldFunction.")

=============================================================================
