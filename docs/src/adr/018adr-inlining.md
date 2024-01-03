# ADR-018: Inlining in Apalache

| author       | revision  | last revised |
| ------------ | --------: | ------------ |
| Jure Kukovec | 1         | 2022-04-21   |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

<!-- Statement to summarize, following the following formula: -->

This ADR defines the various kinds of inlining considered in Apalache and discusses the pros and cons of their implementations.
Since we have recently reworked the inliner in [#1569](https://github.com/informalsystems/apalache/pull/1569), we saw it fit to document exactly how inlining is supposed to work and we have chosen the transformations performed in the inlining pass. 

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->

TLA+ allows the user to define their own operators (e.g. `A`), in addition to the standard ones built into the language itself (e.g. `\union`).
This can be done either globally, where the module directly contains a definition, or locally via LET-IN, where a local operator is defined within the body of another operator. For example:
```tla
GlobalA(p, q) ==
  LET LocalB(r) == r * r
  IN LocalB(p + q)
```

defines a global operator `GlobalA`, within which there is a locally defined `LocalB`.

Suppose we are given an invariant `GlobalA(1,2) = 9`. How do we evaluate whether or not this invariant holds? To do that, we need to evaluate 
`LET LocalB(r) == r * r IN LocalB(p + q)`, and to do _that_, we need to evaluate `LocalB(p + q)`. 
However, we cannot evaluate `LocalB(p + q)` in a vacuum, because `p` and `q` are not values we can reason about, but instead formal parameters. 
What we need to do, is determine the value of "`LocalB(p + q)`, if `p = 1` and `q = 2`". In other words, we need to apply the substitution `{p -> 1, q ->2}` to `LocalB(p + q)`, which gives us `LocalB(1 + 2)`. 
Repeating this process, we apply the substitution `{r -> 1 + 2}` to 
`r * r`, the body of `LocalB`, to obtain the following equivalence:
```tla
GlobalA(1,2) = 9 <=> (1 + 2) * (1 + 2) = 9
```

The process of applying these substitutions as syntactic transformations is called inlining. 

More precisely, suppose we are given a _non-recursive_ operator `A` with the following definition:
```tla
A(p1,...,pn) == body
```

The term "inlining" (of `A`) typically refers to the process of replacing instances of operator application `A(e1,...,en)` with `body[e1/p1,...,en/pn]`, i.e. the expression obtained by replacing each instance of `pi` with `ei` within `body`.
We elect to use the term in a broader sense of "replacing an operator with its definition", and define two "flavors" of inlining:
  1. Standard inlining: the instantiation described above
      1. Non-nullary inlining: the instantiation described above, except the inlining skips nullary LET-defined operators
  2. Pass-by-name inlining: replacing an operator name `A` used as an argument to a higher-order operator with a local LET-definition: `LET A_LOCAL(p1,...,pn) == A(p1,...,pn) IN A_LOCAL`

The reason for doing (1) is that, at some point, a rewriting rule would have to generate constraints from `A(e1,...,en)`. 
To do this, we couldn't just separately encode `body` and `e1,...,en`, because the richness of the data structures allowed in TLA+ makes it difficult to combine independently generated constraints, in cases where the operator parameters are complex expressions (e.g. `e1` is some record with varied nested constructs).
This is mostly due to the fact that there is no 1-to-1 correspondence between TLA+ objects and SMT datatypes, so encoding object equality is more complicated (which would be needed to express that `ei` instantiates `pi`).
Therefore we must, no later than at the point of the rewriting rule, know `body[e1/p1,...,en/pn]`. 

While inlining non-nullary operators is strictly necessary, inlining nullary operators is not, because nullary operators, by definition, do not have formal parameters. 
Therefore, in a well-constructed expression, all variables appearing in a nullary operator are scoped, i.e. they are  either specification-level variables (defined as `VARIABLE`), or bound in the context within which the operator is defined, if local. An example of the latter would be `i` in 
```tla
\E i \in S: LET i2 == i * i in i2 = 0
```
which is not bound in the nullary operator `i2`, but it is defined in the scope of the `\E` operator, under which `i2` is defined. Therefore, any analysis of `i2` will have `i` in its scope.
The non-nullary variant of (1) is therefore strictly better for performance, because it allows for a sort of caching, which avoids repetition. Consider for example:
```tla
A1(p) == 
  LET pCached == p
  IN F(pCached,pCached)

A2(p) == F(p,p)
```

If we apply the substitution `{p -> e}`, for some complex value `e`, to the bodies of both operators, the results are 

```tla
LET pCached == e
IN F(pCached,pCached)
```
and
```
F(e,e)
```

In the first case, we can translate `pCached` to a cell (Apalache's SMT representation of TLA+ values, see [this
paper](https://dl.acm.org/doi/10.1145/3360549) for details) and reuse the cell expression twice, whereas in the second, `e` is rewritten twice, independently.
So in the case that we perform (1), we will always perform the non-nullary variant, because it is strictly more efficient in our cell-arena framework fo rewriting rules.

The reason for doing (2) is more pragmatic; in order to rewrite expressions which feature any of the higher-order (HO) built-in operators, e.g. `ApaFoldSet(A, v, S)`, we need to know, at the time of rewriting, how to evaluate an application of `A` (e.g. `A(partial, current)` for folding). 
Performing (2) allows us to make the rewriting rule local, since the definition becomes available where the operator is used, and frees us from having to track scope in the rewriting rules.

### Examples
Suppose we have an operator 
```tla
A(p,q) == p + 2 * q
```

Then, the result of performing (1) for `A(1, 2)` would be `1 + 2 * 2`. 
The constant simplification could take the inlined expression and simplify it to `5`, whereas it could not do this across the application boundary of `A(1,2)`.

The result of performing (2) for `ApaFoldSet(A, 0, {1,2,3})` would be
```tla
ApaFoldSet(LET A_LOCAL(p,q) == p + 2 * q, 0, {1,2,3})
```

While this resulting expression isn't subject to any further simplification, notice that it _does_ contain all the required information to fully translate to SMT, unlike `ApaFoldSet(A, 0, {1,2,3})`, which requires external information about `A`.

## Options

<!-- Communicate the options considered.
     This records evidence of our circumspection and documents the various alternatives
     considered but not adopted.
-->
Knowing that we must perform (1) at some point, what remains is to decide whether we perform inlining on-demand as part of rewriting, or whether to isolate it to an independent inlining-pass (or as part of preprocessing), i.e. performing a syntactic transformation on the module, that replaces `A(e1,...,en)` with `body[e1/p1,...,en/pn]`, or merely generating rewriting rules that _encode_ `A(e1,...,en)` equivalently as `body[e1/p1,...,en/pn]`, while preserving the specification syntax.
Additionally, if we do isolate inlining to a separate pass, we can choose whether or not to perform (2).

1. Perform no inlining in preprocessing and inline only as needed in the rewriting rules.
    - Pros: Spec intermediate output remains small, since inlining increases the size of the specificaiton
    - Cons: 
      - Fewer optimizations can be applied, as some are only applicable to the syntactic forms obtained after inlining (e.g. `ConstSimplifier` can simplify `IF TRUE THEN a ELSE b`, but not `IF p THEN a ELSE b`)
      - Rewriting rules for different encodings have to deal with operators in their generality.

1. Independently perform only standard (non-nullary) inlining (1), but no pass-by-name inlining (2)
    - Pros: Allows for additional optimizations after inlining (simplification, normalization, keramelization, etc.)
    - Cons: Rewriting rules still need scope, to resolve higher-order operator arguments in certain built-in operators (e.g. folds)
    - Recall that the non-nullary variant of (1) is strictly better than the simple one (while being trivial to implement), because nullary inlining is prone to repetition.


1. Independently perform non-nullary inlining and pass-by-name inlining
    - Pros: 
        - Enables further optimizations (simplification, normalization, keramelization, etc.)
        - Using non-nullary inlining has all of the benefits of standard inlining, while additionally being able to avoid repetition (e.g. not inlining `A` in `A + A`)
        - Pass-by-name inlining allows us to keep rewriting rules local
    - Cons: Implementation is more complex

## Solution

<!-- Communicates what solution was decided, and it is expected to solve the
     problem. -->

We elect to implement option (3), as most of its downsides are developer burdens, not theoretical limitations, and its upsides (in particular the ones of non-nullary inlining) are noticeable performance benefits.
Maintaining local rewriting rules is also a major technical simplification, which avoids potential bugs with improperly tracked scope.

## Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

TBD
