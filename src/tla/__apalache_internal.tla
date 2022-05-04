------------------- MODULE __apalache_internal --------------------------------
(*
 * This is an internal module that exposes Apalache operators that are
 * needed for rewiring the standard modules and the community modules.
 *
 * DO NOT USE THIS MODULE IN YOUR SPECIFICATIONS.
 *
 * We may change this module as much as we need and as often as we like.
 *)

(**
 * Return the capacity of a sequence (a static upper bound on its length).
 *
 *
 * @type: Seq(a) => Int;
 *)
__ApalacheSeqCapacity(__seq) ==
    \* A dummy implementation.
    \* Apalache binds it to ApalacheInternalOper.apalacheSeqCapacity.
    0

(**
 * This operator is well-typed, but as soon as it reaches the model checker,
 * the model checker should print the message and stop. The type checker should
 * be able to process this operator.
 *
 * @type: Str => a;
 *)
__NotSupportedByModelChecker(__msg) ==
    \* A dummy implementation.
    \* Apalache binds it to ApalacheInternalOper.notSupportedByModelChecker.
    CHOOSE __x \in {}: TRUE

===============================================================================
