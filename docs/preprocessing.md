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
 * `PrimedEqualityToMembership`: replaces `x = e` with `x \in {e}` (required by `TransitionPass`)
 * `ExprOptimizer`: statically computes select expressions (e.g. record field access from a known record)
 * `ConstSimplifier`: propagates constants
 
 ## Keramelizer
 
 Keramelizer rewrites TLA+ expressions into [KerA](./kera.md). For many TLA+ expressions
 this translation is clear, however, some expressions cannot be easily translated. Below
 we discuss such expressions and the decisions that we have made.
 
 ### CASE <a name="kera-case"></a>
 
 TLA+ supports two kinds of CASE expressions:
 
   * `CASE`. These are expressions without a default value:
   
```tla
    CASE
         p_1 -> e_1
      [] p_2 -> e_2
         ...
      [] p_n -> e_n
```   
   
   * `CASE-OTHER`. These are expressions with a default value:

```tla
   CASE
        p_1 -> e_1
     [] p_2 -> e_2
        ...
     [] p_n -> e_n
     [] OTHER -> e_def
```   

Keramelizer supports only `CASE-OTHER` and asks the user to translate `CASE` expressions
into `CASE-OTHER`. One could imagine that `CASE` could be expressed as
```(p_1 /\ e_1) \/ ... \/ (p_n /\ e_n)```. However, this approach only works for Boolean
expressions, which requires type inference. Moreover, the user expects a warning when
neither of the conditions `p_1, ..., p_n` holds true.
Hence, Leslie Lamport defines semantics of case in [Specifying Systems, p. 298](#spec2004) as:

```tla
  CHOOSE v: (p_1 /\ (v = e_1) \/ ... \/ (p_n /\ (v = e_n)))
```

Similarly, `CASE-OTHER` is defined  as:
 
 ```tla
  CHOOSE v: (p_1 /\ (v = e_1) \/ ... \/ (p_n /\ (v = e_n)) \/ (~p_1 /\ ... ~p_n /\ (v = e_ def)))
 ```
 
As a result, if there are several conditions among `p_1, ..., p_n` that hold true,
then `CHOOSE` always selects the same condition ```p_i``` for equivalent formulas.
_It is hard to enforce these general semantics in a model checker_. Thus, we have decided to select
a fixed order of evaluating the conditions: the top-to-bottom order that is commonly used in
programming languages. By using this approach, it is easy to translate `CASE-OTHER` as follows:

```tla
IF p_1
THEN e_1
ELSE
  IF p_2
  THEN e_2
  ...
    IF p_n
    THEN e_n
    ELSE e_def
```

With this approach it is not obvious how one would translate `CASE` in a sound way.
We could drop the last condition `p_n` and unconditionally use the expression `e_n` in the bottom
else arm. Hence, we ask the user to add the `OTHER` case to a `CASE` expression. Usually,
the user has a better idea about the default case than an automatic tool. For instance,
one can also rewrite the (presumably impossible) default case using the `CHOOSE` operator:

```tla
   CASE
        p_1 -> e_1
     [] p_2 -> e_2
        ...
     [] p_n -> e_n
     [] OTHER -> CHOOSE x \in {}: FALSE
```   


  

# References

 * Leslie Lamport. Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers.
Addison-Wesley Professional, 2004. <a name="spec2004"></a>
