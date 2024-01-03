# PDR-017: Checking temporal properties

| authors                                | last revised    |
| -------------------------------------- | --------------: |
| Igor Konnov, Philip Offtermatt         | 2022-04-01      |

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

There are multiple ways to encode the constraints by [Biere et al. 2006][].
The different ways are demonstrated on the [EWD998](EWD998.tla) spec,
which specifies a protocol for termination detection,
using token passing in a ring.

#### **Trace Invariants**
 The lasso finding problem can be encoded as a [trace invariants][]. See e.g. the [EWD998 protocol with trace invariants](EWD998_trace.tla).
 Roughly, a loop is encoded by demanding there exists a loop index at which point the state is identical to the state at the end of the execution.

 Implementation details:
 - Instead of quantifying over indices, one could use an additional Boolean variable starting out FALSE that nondeterministically guesses when the execution enters the loop and is set to TRUE at that point. Experiments suggest this negatively impacts performance, but it can help understand counterexamples, since the loop is immediately visible in the states.
   
  Advantages:
  - The predicate in the spec is very close to the semantic meaning of the temporal operators, e.g. `[] x >= 2` becomes `\A step \in DOMAIN hist: hist[step].x >= 2`
  - Only very few new variables are added (none, but depending on implementation choices maybe one/two).

  Disadvantages:
  - Trace invariants require Apalache to pack the sequence of states.
    This sometimes produces unnecessary constraints.

  - When a trace invariant is violated, the intermediate definitions
    in this invariant are not printed in the counterexample.
    This will make printing of the counterexamples to liveness harder, e.g. see an [example](counterexample_trace.tla#L118)


#### **Encoding with auxiliary variables**

The loop finding problem can alternatively be approached
by adding extra variables: One variable `InLoop` which
determines whether the execution is currently on the loop,
and for each variable `foo` of the original spec an extra variable `loop_foo`,
which, once `InLoop` is true, stores the state of `foo` at the start of the loop.
Then, the loop has been completed if `vars = loop_vars`.

Apart from the variables for finding the loop, this approach also needs extra variables for
determining the satisfaction of the temporal property to be checked.
There again exist multiple ways of concretely implementing this:

##### **Encoding with Buchi automata**
One can extend the spec with a Buchi automaton
which is updated in each step. The Buchi automaton encodes
the negation of the temporal property, thus if the automaton
would accept, the property does not hold.
By checking whether an accepting state of the automaton is seen
on the loop, it can be determined whether the automaton
accepts for a looping execution.
The encoding is described in [Biere et al. 2002][]
See e.g. the [EWD998 protocol with a Buchi automaton](EWD998_buchi.tla).

Implementation details:
- An implementation of this encoding would need an implementation of an algorithm for the conversion from LTL to Buchi automata.
This could be an existing tool, e.g. [Spot](https://spot.lrde.epita.fr/) or our own implementation.

Advantages:
- Buchi automata for very simple properties can be simple to understand
- Underlying automata could be visualized
- Only needs few extra variables - the state of the Buchi automaton can easily be encoded as a single integer

Disadvantages: 
- Can be slow: Buchi automata generally exhibit either nondeterminism or can get very large
- Hard to understand: Engineers and even experts have a hard time intuitively understanding Buchi automata for mildly complicated properties

##### **Tableau encoding**
One can instead extend the spec with auxiliary Boolean variables
roughly corresponding to all nodes in the syntax tree who have temporal operators
beneath them. The value of each variable in each step corresponds to whether the
formula corresponding to that node in the syntax tree is satisfied from that point forward. The encoding is described in Section 3.2 of [Biere et al. 2006][]
See e.g. the [EWD998 protocol encoded with a tableau](EWD998_tableau.tla).

Implementation details:
- Naming the auxiliary variables is very important, since they are supposed to represent the values of complex formulas (ideally would simple have that formula as a name, but this is not syntactically possible for most formulas), and there can be many of them.


Advantages:
- Very clear counterexamples: In each step, it is clearly visible which subformulas are or are not satisfied.
- Relatively intuitive specs: The updates to the auxiliary variables
correlate with the intuitive meaning of their subformulas rather directly
in most cases

Disadvantages: 
- Many variables are added: The number of variables is linear in the number of operators in the formula
- Specifications get long: The encoding is much more verbose than that for Buchi automata

#### **Decision - which encoding should be used?**

We chose to implement the tableau encoding, since it produces the
clearest counterexamples. Buchi automata are hard to understand. 
For trace invariants, the lack of quality in counterexamples makes it
very hard to debug and understand invariant violations.

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
[Model Checking]: https://mitpress.mit.edu/books/model-checking-second-edition
[Padon et al. 2021]: https://link.springer.com/article/10.1007/s10703-021-00377-1
[Biere et al. 2002]: http://fmv.jku.at/papers/BiereArthoSchuppan-FMICS02.pdf
