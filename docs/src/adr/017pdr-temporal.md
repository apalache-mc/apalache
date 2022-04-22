---
authors: Igor Konnov
last revised: 2022-04-01
---

# PDR-017: Checking temporal properties

**This is a preliminary design document. It will be refined and it will mature
  into an ADR later.**

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

The "TLA" in TLA+ stands for *Temporal Logic of Actions*, whereas the plus sign
(+) stands for the rich syntax of this logic. So far, we have been focusing on
the *plus* of TLA+ in Apalache. Indeed, the repository of [TLA+ Examples][]
contains a few occurrences of temporal properties.

In this PDR, we lay out a plan for implementing support for model checking
of temporal properties in Apalache.

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->

Apalache supports checking of several kinds of invariants: [state, action, and
trace invariants][]. Some of the TLA+ users do not want to be limited by
invariants, but want to write temporal properties, which let them express
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

   - `ENABLED A`, for an action formula `A`, is true in a state `s` if
     there is a state `t` such that `s` is transformed to `t` via action `A`.

 - **Temporal formulas**:

   - Eventually: `<>F`, for a temporal formula `F`.

   - Always: `[]F`, for a temporal formula `F`.

   - Weak fairness: `WF_e(A)`, for an expression `e` and a formula `F`,
        which is equivalent to `[]<>~(ENABLED <A>_e) \/ []<><A>_e`.

   - Strong fairness: `SF_e(A)`, for an expression `e` and a formula `F`,
        which is equivalent to `<>[]~(ENABLED <A>_e) \/ []<><A>_e`.

   - Leads-to: `F ~> G`, which is equivalent to `[](F => <>G)`.

Technically, TLA+ also contains four other operators that are related to
temporal properties: `A \cdot B`, `\EE x: F`, `\AA x: F`, and `F -+-> G`. These
very advanced operators appear so rarely that we ignore them in this work.
Most likely, For their semantics, check [Specifying Systems][] (Section
16.2.3-4).

## Design space

SAT encodings of bounded model checking for LTL are a textbook material. A
linear encoding for LTL is presented in the paper [Biere et al. 2006][]. It is
explained in [Handbook of Satisfiability][] (Chapter 14). Hence, we do not have
to do much research around this. However, we have to adapt the standard
techniques to the domain of TLA+. For instance, we have to understand how to
deal with `ENABLED`, `WF`, and `SF`, which deviate from the standard setting of
model checking.

Viktor Sergeev wrote the [first prototype][] for liveness checking at
University of Lorraine in 2019. Since his implementation was tightly integrated
with the exploration algorithm, which was refactored several times, this
implementation has not been integrated in the main branch. We have learned from
this prototype and discuss our options under this angle.

There are two principally different approaches to the implementation of
temporal model checking:

 1. Tight integration with [Transition Executor][].

    In this approach, we would extend the transition executor to incrementally
    check LTL properties via the encoding by [Biere et al. 2006][]. This
    approach would let us implement various optimizations. However, it would be
    harder to maintain and adapt, as we have seen from the first prototype.

 1. Specification preprocessing.

    In this approach, given a specification `S` and a temporal property `P`, we
    would produce another specification `S_P` and an invariant `I_P` that has
    the following property: the temporal property `P` holds on specification
    `S` if and only if the invariant `I_P` holds on specification `S_P`.  In
    this approach, we encode the constraints by [Biere et al. 2006][] directly
    in TLA+. The potential downside of this approach is that it may be less
    efficient than the tight integration with the transition executor.

We choose the second approach via specification preprocessing. This will
simplify maintenance of the codebase. Additionally, the users will be able to
see the result of preprocessing and optimize it, if needed. When the new
implementation is well understood, we can revisit it and consider Option 1,
once [ADR-010][] is implemented.

## Work plan

The work plan is tracked in the [issue on temporal properties][].

We propose to split this work into two big subtasks:

 - *Task 1. Temporal operators*:
    Support for `<>P`, `[]P`, `<A>_e`, and `[A]_e` via preprocessing.

 - *Task 2. Fairness*:
    Support for `ENABLED A`, `WF_e(A)`, and `SF_e(A)` via preprocessing.

The task on *Temporal operators* is well-understood and poses no technical
risk. By having solved Task 1, we can give users a relatively complete toolset
for safety and liveness checking. Indeed, even fairness properties can be
expressed via `<>` and `[]`.

To support temporal reasoning as it was designed by Leslie Lamport, we have to
solve Task 2. Most likely, we will have to introduce additional assumptions
about specifications to solve it.

### 1. Temporal operators

This task boils down to the implementation of the encoding explained in [Biere
et al. 2006][].

In model checking of temporal properties, special attention is paid to lasso
executions. A *lasso* execution is a sequence of states `s[0], s[1], ..., s[l],
..., s[k]` that has the following properties:

  - the initial state `s[0]` satisfies `Init`,
  - every pair of states `s[i]` and `s[i+1]` satisfies `Next`, for `i \in 0..k-1`,
    and
  - the loop closes at index `l`, that is, `s[l] = s[k]`.

The lasso executions play an important role in model checking, due to the lasso
property of finite-state systems:

    Whenever a finite-state transition system `M` violates a temporal property
    `F`, this system has a lasso execution that violates `F`.

You can find a proof in the book on [Model Checking][]. As a result, we can
focus on finding a lasso as a counterexample to the temporal property.
Importantly, this property holds only for finite-state systems. For example, if
all variable domains are finite (and bounded), then the specification is
finite-state. However, if a specification contains integer variables, it may
produce infinitely many states. That is, an infinite-state system may still
contain lassos as counterexamples but it does not have to, which makes this
technique incomplete. An extension to infinite-state systems was studied by
[Padon et al. 2021][]. This is beyond the scope of this task.

There are two ways to encode the constraints by [Biere et al. 2006][]:

 1. Encode the lasso finding problem as a trace invariant. Apalache can check
 [trace invariants][]. This approach is most straighforward. However it has
 several drawbacks:

    - Trace invariants require Apalache to pack the sequence of states.
      This sometimes produces unnecessary constraints.

    - When a trace invariant is violated, the intermediate definitions
      in this invariant are not printed in the counterexample.
      This will make printing of the counterexamples to liveness harder.

 1. Instrument the existing specification by adding auxilliary variables that
 update the predicates as required by the encoding of [Biere et al. 2006][].
 We could also extend it with the liveness-to-safety reduction, see [Biere et
 al. 2006][]. If we choose this approach, we will be able to print
 counterexamples. So this approach is more transparent.

To choose between these two approaches, we will try both of them on a simple
specification. For instance, [Folklore broadcast][].

### Encoding with Trace Invariants
[Folklore with trace invariants] is relatively straightforward.
Some implementation choices that might be altered depending on solver performance are:
* The `LoopSelector` is a boolean variable. One could alternatively use an integer to 
denote the index of the loop start, or not have a global variable for this and instead
use a LET IN definition like `LET loopStart == GUESS x \in {candidate \in DOMAIN hist: hist[candidate].vars = vars}`. With this choice, one would have to be careful that the loop index is the same across subformulas. Additionally, it is important that GUESS is nondeterministic, not deterministic-but-arbitrary.  
* The spec uses two auxiliary variables, `LoopSelector` and `InLoop`.
`InLoop` is not necessary, but it can be used to ensure `LoopSelector` is
true only in a single state without an additional mutual exclusion constraint.

Advantages of the encoding using trace invariants:
* (In my opinion) they remain very close to the formal semantics of the temporal operators 
* Thus, it might be easier to understand how the temporal operators are encoded
when one looks at the intermediate outputs of Apalache.
* Trace invariants can be used very flexibly, 
so someone who understands only temporal operators, but then takes time to
learn about trace invariants, may be able to reuse trace invariants for other use cases

Disadvantages:
* Invariant violations in counterexamples for trace invariants are not displayed properly (see [Trace invariant counterexample] )
* Trace invariants seem like they lead to additional constraints, so they might be slower than a propositional encoding


### 2. Fairness

`WF_e(A)` and `SF_e(A)` use `ENABLED(A)` as part of their definitions. Hence,
`ENABLED(A)` is of ultimate importance for handling `WF` and `SF`. However, we
do not know how to efficiently translate `ENABLED(A)` into SMT. A
straightforward approach requires to check that for all combinations of state
variables `A` does not hold.

This work requires further research, which we will do in parallel with the
first part of work. To be detailed later...

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
[issue on temporal properties]: https://github.com/informalsystems/apalache/issues/488
[trace invariants]: ../apalache/principles/invariants.md#trace-invariants
[Folklore broadcast]: https://github.com/tlaplus/Examples/blob/master/specifications/bcastFolklore/bcastFolklore.tla
[Model Checking]: https://mitpress.mit.edu/books/model-checking-second-edition
[Padon et al. 2021]: https://link.springer.com/article/10.1007/s10703-021-00377-1
[Folklore with trace invariants]: ../../../test/tla/bcastFolklore_trace.tla
[Trace invariant counterexample]: ../../../test/tla/bcastFolklore_trace_counterexample.tla#L150
