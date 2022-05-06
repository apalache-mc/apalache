-------------------- MODULE __apalache_folds ----------------------------------
(*
 * This is an internal module that is used to resolve circular dependencies
 * between Apalache, Sequences, and Community modules. Do not use this module.
 *)

(**
 * A copy of Apalache!ApaFoldSet, which should be used only in Apalache rewirings.
 *
 * The folding operator, used to implement computation over a set.
 * Apalache implements a more efficient encoding than the one below.
 * (from the community modules).
 *
 * @type: ((a, b) => a, a, Set(b)) => a;
 *)
__ApalacheFoldSet(__Op(_, _), __v, __S) ==
    \* A dummy implementation. Apalache rewires it with ApalacheOper.foldSet.
    __v

(**
 * A copy of Apalache!ApaFoldSeqLeft, which should be used only in Apalache rewirings.
 *
 * The folding operator, used to implement computation over a sequence.
 * Apalache implements a more efficient encoding than the one below.
 * (from the community modules).
 *
 * @type: ((a, b) => a, a, Seq(b)) => a;
 *)
__ApalacheFoldSeq(__Op(_, _), __v, __seq) ==
    \* A dummy implementation. Apalache rewires it with ApalacheOper.foldSeq.
    __v

(**
 * A sequence constructor that avoids using a function constructor.  This
 * operator creates the sequence `<<F(1), F(2), ..., F(N)>>` for a constant
 * expression `N`.  This operator is more efficient than the indirect
 * application of `FunAsSeq([ i \in 1..N |-> F(i) ])`.
 *
 * @type: (Int, (Int -> a)) => Seq(a);
 *)
__ApalacheMkSeq(__N, __F(_)) ==
  \* A dummy implementation. Apalache rewires it with ApalacheOper.mkSeq.
  <<>>

===============================================================================
