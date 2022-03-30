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
the plus aspect of TLA+ in Apalache. Indeed, the repository of [TLA+
Examples][] contains a few occurrences of temporal properties.

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
properties can be found in [Specifying Systems][][16.2.3, 16.2.4]. In short, temporal formulas
are Boolean combinations of the following kinds of subformulas:

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

   - `A \cdot B` (we ignore it).

 - **Temporal formulas**:

   - Eventually: `<>F`, for a temporal formula `F`.

   - Always: `[]F`, for a temporal formula `F`.

   - Weak fairness: `WF_e(A)`, for an expression `e` and a formula `F`,
        which is equivalent to `[]<>~(ENABLED <A>_e) \/ []<><A>_e`.

   - Strong fairness: `SF_e(A)`, for an expression `e` and a formula `F`,
        which is equivalent to `<>[]~(ENABLED <A>_e) \/ []<><A>_e`.

   - Leads-to: `F ~~> G`, which is equivalent to `[](F => <>G)`.

## Options

<!-- Communicate the options considered.
     This records evidence of our circumspection and documents the various alternatives
     considered but not adopted.
-->

## Solution

<!-- Communicates what solution was decided, and it is expected to solve the
     problem. -->

## Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

[TLA+ Examples]: https://github.com/tlaplus/Examples
[BHHLS06]: https://lmcs.episciences.org/2236
[state, action, and trace invariants]: ../apalache/principles/invariants.md
[Specifying Systems]: https://lamport.azurewebsites.net/tla/book.html
