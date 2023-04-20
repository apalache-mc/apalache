# ADR-024: Arena computation isolation

| authors                                | last revised    |
| -------------------------------------- | --------------: |
| Jure Kukovec                           | 2023-04-20      |

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

The core of the model checking pass -- the rewriting rules -- have shown to be a significant hurdle to onboarding, maintenance and modification efforts.
Relevant for this ADR is the fact that rewriting rules do multiple things at once, which are difficult to separate. They:
  1. Modify arenas
  2. Push constraints into SMT
  3. Manipulate bindings

Most notably, we have an interaction between arenas and SMT; adding edges to an arena sometimes results in the creation of new SMT variables, or the assertion of new SMT constraints.
As a result, arenas are incredibly fragile, as it becomes easy to inadvertently create problematic constraints, e.g. by forgetting to manually create SMT constants before using them, or by omitting an assertion which was expected with a given change to the arena.

However, we observe that this relationship should, theoretically, be unidirectional; access to SMT is not required in order to correctly construct an arena for a given BMC problem (though finding a model, or lack thereof, requires the generation of SMT constraints, based off the arena).

This ADR seeks to explore ways in which arena construction and SMT concerns may be separated.

## Options

<!-- Communicate the options considered.
     This records evidence of our circumspection and documents the various alternatives
     considered but not adopted.
-->

1. Redesign the interface of rewriting rules/arenas/solver contexts, to better identify interacting with mutable state. Rewriting rules only get access to a limited mutable state interface, and all the interactions between SMT and arenas are pushed out of the rules, into the mutable state implementation.
2. Extract arena generation into a separate static analysis pass. Change the rewriting rules, such that they read from a fixed arena object on demand. Optionally also abstract discharging constraints, to relieve the dependency on Z3-specific constructs.
3. Compute arenas and generate SMT constraints in a single tree-exploration pass, but stratify the rewriting rules, such that arena generation and SMT operators for a given rule are clearly separated.


## Solution

<!-- Communicates what solution was decided, and it is expected to solve the
     problem. -->

After initially exploring [(2)](#consequences), we have decided to ultimately implement option (3). The reasons for this decision are threefold:
  - Memory: As this exploration traverses the tree exactly once, no persistent storage between passes ever needs to exist, and thus the memory footprint is greatly reduced. Additionally, during performance discussions, we have come to the realization, that computing and holding the entire arena in memory, like how the current implementation does, is actually unnecessary. In fact, only a sub-arena, describing the relevant relations of the cells belonging to an expression sub-tree is ever needed in the scope of that sub-tree.
  - Separation of concerns: While arena generation and SMT aren't separated on the level of a pass, they are still clearly separated within each node exploration step, reaping the benefits of readability and maintainability all the same. Additionally, this form allows us to handle SMT encoding variations (e.g. arrays vs non-arrays) much more elegantly.
  - Refactoring effort: The final form of the new rules will be syntactically much closer to the current rules, and have a much smaller penalty on incremental change, and our ability to compare and evaluate the changes.

## Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

### Isolated arena pass
We initially choose option (2), as we believed it best embodied the "separation of concerns" principle. 
Additionally, the idea was that removing arena computation from the rewriting rules should simplify the rules and result in more clarity, readability, and maintainability.
A prototype can be found [here][proto].

However, separating arena computation into its own pass introduced a new issue, the propagation of information between the arena computation pass and the SMT translation pass that would follow it.
In [Notes][] one can find a more in-depth explanation of the issue and its solutions.
In a nutshell, the problem was that, to retain information from ephemeral expressions, and tie it back to the original syntax tree, we would need a map-of-maps data structure (in the theoretical sense, there potentially exist more efficient tree-like structures at the level of implementation detail, but not by a significant order of magnitude).
Between the two passes, this data structure needs to be stored either in memory or to a file (and read later).

Compared to that, the single-traversal approach of the current rewriting rules
actually has a much better memory footprint, since only the information relevant to the current sub-tree scope needs to be retained.




[Notes]: https://github.com/informalsystems/apalache/pull/2467
[proto]: https://github.com/informalsystems/apalache/tree/jk/arenaSeparationProto/tla-pp/src/main/scala/at/forsyte/apalache/tla/pp/arenas