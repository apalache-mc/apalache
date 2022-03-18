-------------------- MODULE __apalache_folds ----------------------------------
(*
 * This is an internal module that is used to resolve circular dependencies
 * between Apalache, Sequences, and Community modules. Do not use this module.
 *)

(**
 * A copy of Apalache!FoldSet, which should be used only in Apalache rewirings.
 *
 * The folding operator, used to implement computation over a set.
 * Apalache implements a more efficient encoding than the one below.
 * (from the community modules).
 *
 * @type: ((a, b) => a, a, Set(b)) => a;
 *)
__ApalacheFoldSet(Op(_, _), v, S) ==
    \* A dummy implementation. Apalache rewires it with Apalache.foldSet.
    v

(**
 * A copy of Apalache!FoldSeq, which should be used only in Apalache rewirings.
 *
 * The folding operator, used to implement computation over a sequence.
 * Apalache implements a more efficient encoding than the one below.
 * (from the community modules).
 *
 * @type: ((a, b) => a, a, Seq(b)) => a;
 *)
__ApalacheFoldSeq(Op(_, _), v, seq) ==
    \* A dummy implementation. Apalache rewires it with Apalache.foldSeq.
    v

===============================================================================
