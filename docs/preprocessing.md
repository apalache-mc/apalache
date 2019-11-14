# Preprocessing in APALACHE

Before translating a specification into SMT, `apalache` performs a number of
preprocessing steps:
 
 * `InlinerOfUserOper`: replaces every call to user operator with the operator body.
 * `LetInExpander`: replaces every call to a let-definition with the definition body
    (except for the definitions without the arguments).
 * `PrimingPass`: adds primes to variables in `Init` and `ConstInit` (required by `TransitionPass`)
 * `VCGen`: extracts verification from the invariant candidate.
 * `Desugarer`: remove syntactic sugar like short-hand expressions in `EXCEPT`.
 * `Normalizer`: rewrite all expressions in [negation-normal form](https://en.wikipedia.org/wiki/Negation_normal_form).
 * `Keramelizer`: translate TLA+ expressions into the kernel language [KerA](./kera.md).
 * `PrimedEqualityToMembership`: replace `x = e` with `x \in {e}` (required by `TransitionPass`)
 * `ExprOptimizer`: statically compute expressions
 * `ConstSimplifier`: propagate constants
 
 ## Keramelizer
 
 Keramelizer rewrites TLA+ expressions into [KerA](./kera.md). For many TLA+ expressions
 this translation is clear. However, some expressions cannot be easily translated. Below
 we discuss such expressions and the decisions that we made.
 
 ### CASE <a name="kera-case"></a>
 
 TLA+ supports two kinds of CASE expressions:
 
   * `CASE`. These are the expressions without the default case:
   
```tla
    CASE
         p_1 -> e_1
      [] p_2 -> e_2
         ...
      [] p_n -> e_n
```   
   
   * `CASE-OTHER`. These are the expressions with the default case:

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

```CHOOSE v: (p_1 /\ (v = e_1) \/ ... \/ (p_n /\ (v = e_n)))```.

Similarly, `CASE-OTHER` is expressed as:
 
 ```CHOOSE v: (p_1 /\ (v = e_1) \/ ... \/ (p_n /\ (v = e_n)) \/ (~p_1 /\ ... ~p_n /\ (v = e_ def)))```.
 
As a result, if there are several conditions among `p_1, ..., p_n` that hold true,
then `CHOOSE` always selects the same condition ```p_i``` for equivalent formulas.
_It is hard to enforce this general semantics in a model checker_. Thus, we have decided to select
a fixed order of evaluating the condition: this is the top-to-bottom order that is used in
the programming languages. By using this approach, it is easy to translate `CASE-OTHER` as follows:

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
We could drop the last condition `p_n` and unconditionally use expression `e_n` in the bottom
else arm. Hence, we ask the user to add the `OTHER` case to a `CASE` expression. Usually,
the user has a better idea about the default case than the automatic tool. For instance,
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
