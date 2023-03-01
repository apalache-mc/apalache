# ADR-024: Arena computation isolation

| authors                                | last revised    |
| -------------------------------------- | --------------: |
| Jure Kukovec                           | 2023-03-01      |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

<!-- Statement to summarize, following the following formula: -->

In the context of addressing tech debt\
facing increasing difficulties understanding and modifying the BMC pass\
we decided to decouple arena construction from rewriting rules\
to achieve better modularity, readability, and maintainability \
accepting a reasonable time investment into refactoring.\

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->

The core of the model checking pass is tangled and messy; due to its ad-hoc development in the past, classes and dependencies were added incrementally, often in arbitrary, suboptimal ways.
Relevant for this ADR is the fact that rewriting rules do multiple things at once, which are difficult to separate. They:
  1. Modify arenas
  2. Push constraints into SMT
  3. Manipulate bindings

Most notably, we have an interaction between arenas and SMT; adding edges to an arena sometimes results in the creation of new SMT variables, or the assertion of new SMT constraints.
As a result, arenas are incredibly fragile, as it becomes easy to inadvertently create problematic constraints, e.g. by forgetting to manually create SMT constants before using them, or by omitting an assertion which was expected with a given change to the arena.

However, we observe that this relationship should, theoretically, be unidirectional; access to SMT is not required in order to correctly construct an arena for a given BMC problem (though finding a model, or lack thereof, requires the generation of SMT constraints, based off the arena).

This leads us to propose the following change: instead of rewriting rules constructing arenas on the fly in expected lockstep with SMT, we can pre-generate the entire arena, since this construction depends only on a TLA+ specification (`Init/Next/Inv`).

Then, we can use this constructed arena with redesigned rewriting rules, which can read, but not modify, the arena object, and generate the SMT constraints to be solved.


## Options

<!-- Communicate the options considered.
     This records evidence of our circumspection and documents the various alternatives
     considered but not adopted.
-->

1. Redesign the interface of rewriting rules/arenas/solver contexts, to better identify interacting with mutable state. Rewriting rules only get access to a limited mutable stat interface, and all the interactions between SMT and arenas are pushed out of the rules, into the mutable state implementation.
2. Extract arena generation into a separate static analysis pass. Change the rewriting rules, such that they read from a fixed arena object on demand. Optionally also abstract discharging constraints, to relieve the dependency on Z3-specific constructs.


## Solution

<!-- Communicates what solution was decided, and it is expected to solve the
     problem. -->

We choose option (2), as it best embodies the "separation of concerns" principle. 
Additionally, removing arena computation from the rewriting rules should simplify the rules and result in more clarity, readability, and maintainability.

## Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

TBD
