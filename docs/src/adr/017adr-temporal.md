---
authors: Igor Konnov
last revised: 2022-03-28
---

# ADR-017: Support for temporal properties

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

TLA+ stands for *Temporal Logic of Actions*, whereas the plus sign (+) in the
name stands for the rich syntax of this logic. So far, we have been focusing on
the *plus* of TLA+ in Apalache. Indeed, the repository of [TLA+ Examples][]
contains a few occurrences of temporal properties.

In this ADR, we lay out a plan for implementing support for model checking
of temporal properties in Apalache.

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->

Apalache supports checking of several kinds of invariants: [state, action, and
trace invariants][]. Some of the TLA+ users do not want to be limited by
invariants, but want to write temporal properties, which let them to express
safety and liveness more naturally. A detailed description of temporal
properties can be found in [Specifying Systems][] (Sections 16.2.3-4). In
short, temporal formulas are Boolean combinations of the following kinds of
subformulas:

 - **State predicates**:

   - Boolean formulas that do not contain primes.

 - **Action predicates**:
   - Stutter `A`: `[A]_e`, for an action formula `A`
     and an expression `e` (usually a tuple of variables).
     This predicate is equivalent to `A \/ e' = e`.

   - No-stutter `A`: `<A>_e`, for an action formula `A`
     and an expression `e`, which is equivalent to `A /\ e' /= e`.

   - `ENABLED A`, for an action formula `A`. It is true in a state `s`, if
     there is a state `t` such that `s` is tranformed to `t` via action `A`.

   - `A \cdot B`. This language feature is never used, so we ignore it.

 - **Temporal formulas**:

   - Eventually: `<>F`, for a temporal formula `F`.

   - Always: `[]F`, for a temporal formula `F`.

   - Weak fairness: `WF_e(A)`, for an expression `e` and a formula `F`,
        which is equivalent to `[]<>~(ENABLED <A>_e) \/ []<><A>_e`.

   - Strong fairness: `SF_e(A)`, for an expression `e` and a formula `F`,
        which is equivalent to `<>[]~(ENABLED <A>_e) \/ []<><A>_e`.

   - Leads-to: `F ~> G`, which is equivalent to `[](F => <>G)`.

Technically, TLA+ also contains three other operators: `\EE x: F`, `\AA x: F`,
and `F -+-> G`. These very advanced operators appear so rarely that we ignore
them. For their semantics, check [Specifying Systems][] (Section 16.2.4).

## Options

SAT encodings of bounded model checking for LTL are a textbook material. A
linear encoding for LTL is presented in the paper [Biere et al. 2006][]. It is
explained in [Handbook of Satisfiability][] (Chapter 14). Hence, we do not have
to do much research around this. However, we have to adapt the standard
techniques to the domain of TLA+. For instance, we have to understand how to
deal with `ENABLED`, `WF`, and `SF`, which deviate from the standard setting of
model checking.

Viktor Sergeev has written the [first prototype][] for liveness checking at
University of Lorraine in 2019. Since his implementation was tightly integrated
with the exploration algorithm, which was refactored several times, this
implementation has not been integrated in the main branch. We have learned from
this prototype and discuss our options under this angle.

There are two principally different approaches to the implementation of LTL
model checking:

 1. Tight integration with [Transition Executor][].

    In this approach, we would extend the transition executor to incrementally
    check LTL properties via the encoding by [Biere et al. 2006][]. This approach
    would let us implement various optimizations. However, it would be harder
    to maintain and adapt, as we have seen from the first prototype.

 1. Specification preprocessing.

    In this approach, given a specification `S` and a temporal property `P`, we
    would produce another specification `S_P` and an invariant `I_P` that has
    the following property: the temporal property `P` holds on specification
    `S` if and only if the invariant `I_P` holds on specification `S_P`.

We choose the second approach via specification preprocessing. This will
simplify maintenance of the codebase. Additionally, the users will be able to
see the result of preprocessing and optimize it, if needed. When the new
implementation is well understood, we can revisit it and consider Option 1,
once [ADR-010][] is implemented.

## Solution

<!-- Communicates what solution was decided, and it is expected to solve the
     problem. -->

## Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

[TLA+ Examples]: https://github.com/tlaplus/Examples
[Biere et al. 2006]: https://lmcs.episciences.org/2236
[state, action, and trace invariants]: ../apalache/principles/invariants.md
[Specifying Systems]: https://lamport.azurewebsites.net/tla/book.html
[Handbook of Satisfiability]: https://ebooks.iospress.nl/publication/4999
[first prototype]: https://github.com/informalsystems/apalache/tree/feature/liveness
[Transition Executor]: ./003adr-trex.md
[ADR-010]: ./010rfc-transition-explorer.md
