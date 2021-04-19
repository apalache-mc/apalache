# Preprocessing in APALACHE

Before translating a specification into SMT, `apalache` performs a number of
preprocessing steps:

 * `InlinerOfUserOper`: replaces every call to a user-defined operator with the operator's body.
 * `LetInExpander`: replaces every call to a let-in defined operator of arity at least 1 with the operator's body
 * `PrimingPass`: adds primes to variables in `Init` and `ConstInit` (required by `TransitionPass`)
 * `VCGen`: extracts verification conditions from the invariant candidate.
 * `Desugarer`: removes syntactic sugar like short-hand expressions in `EXCEPT`.
 * `Normalizer`: rewrites all expressions in [negation-normal form](https://en.wikipedia.org/wiki/Negation_normal_form).
 * `Keramelizer`: translates TLA+ expressions into the kernel language [KerA](./kera.md).
 * `ExprOptimizer`: statically computes select expressions (e.g. record field access from a known record)
 * `ConstSimplifier`: propagates constants

 ## Keramelizer

 Keramelizer rewrites TLA+ expressions into [KerA](./kera.md). For many TLA+ expressions
 this translation is clear, however, some expressions cannot be easily translated. Below
 we discuss such expressions and the decisions that we have made.


# References

 * Leslie Lamport. Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers.
Addison-Wesley Professional, 2004. <a name="spec2004"></a>
