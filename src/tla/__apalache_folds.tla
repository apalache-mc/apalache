-------------------- MODULE __apalache_folds ----------------------------------
(*
 * This is an internal module that is used to resolve circular dependencies
 * between Apalache, Sequences, and Community modules. Do not use this module.
 *)

(**
 * A copy of Apalache!FoldSet.
 *
 * @type: ((a, b) => a, a, Set(b)) => a;
 *)
__ApalacheFoldSet(Op(_, _), v, S) ==
    \* A dummy implementation. Apalache rewires it with Apalache.foldSet.
    v

(**
 * A copy of Apalache!FoldSeq.
 *
 * @type: ((a, b) => a, a, Seq(b)) => a;
 *)
__ApalacheFoldSeq(Op(_, _), v, seq) ==
    \* A dummy implementation. Apalache rewires it with Apalache.foldSeq.
    v

===============================================================================
