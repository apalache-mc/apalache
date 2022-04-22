# ADR-018: Inlining in Apalache

| author       | revision | last revised |
| ------------ | --------:| ------------ |
| Jure Kukovec |        1 | Apr 21, 2022 |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

<!-- Statement to summarize, following the following formula: -->

This ADR outlines the transformations that happen in the Apalache inliner pass.
Since we have recently reworked the inliner in [#1569](https://github.com/informalsystems/apalache/pull/1569), we saw it fit to document exactly how inlining is supposed to work and why the inlining pass is the way it is. 

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->
Suppose we are given a _non-recursive_ operator `A` with the following definition:
```tla
A(p1,...,pn) == body
```

The term "inlining" (of `A`) typically refers to the process of replacing instances of operator application `A(e1,...,en)` with `body[e1/p1,...,en/pn]`, i.e. the expression obtained by replacing each instance of `pi` with `ei` within `body`.
We elect to use the term in a broader sense of "replacing an operator with its definition", in the two ways listed below:
  1. Standard inlining: the instantiation described above
      1. Non-nullary inlining: the instantiation described above, except the inlining skips nullary LET-defined operators
  2. Pass-by-name inlining: replacing an operator name `A` used as an argument to a higher-order operator with a local LET-definition: `LET A_LOCAL(p1,...,pn) == A(p1,...,pn) IN A_LOCAL`

The reason for doing (1) is that, at some point, a rewriting rule would have to generate constraints from `A(e1,...,en)`. 
To do this, we couldn't just separately encode `body` and `e1,...,en`, because the richness of the data structures allowed in TLA+ makes it difficult to combine independently generated constraints, in cases where the operator parameters are complex expressions (e.g. `e1` is some record with varied nested constructs).
This is mostly due to the fact that there is no 1-to-1 correspondence between TLA+ objects and SMT datatypes, so encoding object equality is more complicated (which would be needed to express that `ei` instantiates `pi`).
Therefore we must, no later than at the point of the rewriting rule, know `body[e1/p1,...,en/pn]`. 

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
1. Perform no inlining in preprocessing and inline only as needed in the rewriting rules.
    - Pros: Spec intermediate output remains small, since inlining increases the size of the specificaiton
    - Cons: 
      - Fewer optimizations can be applied, as some are only applicable to the syntactic forms obtained after inlining (e.g. `ConstSimplifier` can simplify `IF TRUE THEN a ELSE b`, but not `IF p THEN a ELSE b`)
      - Rewriting rules for different encodings have to deal with operators in their generality.

1. Perform only standard (non-nullary) inlining (1), but no pass-by-name inlining (2)
    - Pros: Allows for additional optimizations after inlining (simplification, normalization, keramelization, etc.)
    - Cons: Rewriting rules still need scope, to resolve higher-order operator arguments in certain built-in operators (e.g. folds)
    - Note that the non-nullary variant of (1) is strictly better than the simple one (while being trivial to implement), because nullary inlining is prone to repetition.


1. Perform non-nullary inlining and pass-by-name inlining
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
