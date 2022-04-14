# ADR-018: Inlining

| author     | revision | last revised |
| ------------ | --------:| -------- |
| Jure Kukovec |    1 | Apr 13, 2022 |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

<!-- Statement to summarize, following the following formula: -->

This ADR outlines the transformations that happen in the Apalache inliner pass.
Since we have recently reworked the inliner in #1569, we saw it fit to document exactly how inlining is supposed to work and why the inlining pass is the way it is. 

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->
The term "inlining" typically refers to the process of replacing instances of operator application `A(x1,...,xn)`, with `e[x1/p1,...,xn/pn]` - the expression obtained by replacing each instance of `pi` with `xi` -  where the operator `A` is defined as `A(p1,...,pn) == e` and is _non-recursive_.
We elect to use the term in a broader sense of "replacing an operator with its definition", in the two ways listed below:
  1. Standard inlining: the instantiation described above
      1. Non-nullary inlining: the instantiation described above, except the inlining skips nullary LET-defined operators
  2. Pass-by-name inlining: replacing an operator name `A` with a local LET-definition: `LET A_LOCAL(p1,...,pn) == A(p1,...,pn) IN A_LOCAL`

The reason for doing (1) is that, in order to encode `A(x1,...,xn)`, we need to know `e[x1/p1,...,xn/pn]`, not just `e`, since the latter may contain free variables (e.g. `x1` is free in `e`).

The reason for doing (2) is more pragmatic; In order to rewrite expressions which feature any of the higher-order (HO) built-in operators, e.g. `ApaFoldSet(A, v, S)`, we need to know, at the time of rewriting, how to evaluate an application of `A` (e.g. `A(partial, current)` for folding). 
Performing (2) allows us to make the rewriting rule local, since the definition becomes available where the operator is used, and frees us from having to track scope in the rewriting rules.

## Options

<!-- Communicate the options considered.
     This records evidence of our circumspection and documents the various alternatives
     considered but not adopted.
-->
1. Perform no inlining in preprocessing and inline only as needed in the rewriting rules.
    - Pros: Spec intermediate output remains small, since inlining increases the size of the specificaiton
    - Cons: Fewer optimizations can be applied, as some are only applicable to the syntactic forms obtained after inlining

1. Perform only standard inlining (1)
    - Pros: Allows for additional optimizations after inlining
    - Cons: Rewriting rules still need scope, to resolve higher-order operator arguments in certain built-in operators (e.g. folds)

1. Perform non-nullary inlining and pass-by-name inlining
    - Pros: 
        - Enables further optimizations 
        - Using non-nullary inlining has all of the benefits of standard inlining, while additionally being able to avoid repetition (e.g. inlining `A` in `A + A`)
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
