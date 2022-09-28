# ADR-023: Trace evaluation

| authors                                | last revised    |
| -------------------------------------- | --------------: |
| Jure Kukovec                           | 2022-09-28      |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

<!-- Statement to summarize, following the following formula: -->

In the context of improving usability\
facing difficulties understanding counterexample traces\
we decided to implement trace evaluation\
to achieve a better user experience\
accepting the development costs.\

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->
As explained in [#1845](https://github.com/informalsystems/apalache/issues/1845), one often runs into the problem of unreadable counterexamples; 
for complex specifications, it is often the case that either the sate contains many variables, or the invariant contains many conjunctive components (or both).
In that case, trying to determine exactly why e.g. `A1 /\ ... /\ An` was violated basically boils down to manually evaluating each formula `Ai` with whatever variables are present in the state.
This is laborious and error-prone, and should be automated.


## Options

<!-- Communicate the options considered.
     This records evidence of our circumspection and documents the various alternatives
     considered but not adopted.
-->
1. Call REPL in each state:
    - No convenient REPL integration at the moment
    - No clear way of saving outputs
1. Encode trace traversal as an Apalache problem and use the solver
    - No additional rules or IO needed

## Solution

<!-- Communicates what solution was decided, and it is expected to solve the
     problem. -->

We choose option (2). 

Suppose we are given a trace `s0 -> s1 -> ... -> sn` over variables `x1,...,xk` as well as expressions `E1,...,Em`, such that all free variables of `E1,...,Em` are among `x1,...,xk`. W.l.o.g. assume all constants are inlined.

The above defines a trace `t0 -> t1 -> ... -> tn` over variables `v1,...,vm`, such that 
```
ti.vj = Ej[si.x1/x1,...,si.xk/xk]
```

for all `i \in 0..n, j \in 1..m`. In other words, `vj` in state `ti` is the evaluation of the expression `Ej` in state `si`.

By using TransitionExecutor instead of a generic Next-decomposition, this can be encoded as a specification free of control-nondeterminism, in-state computation, or invariants, and is thus incredibly efficient to represent in SMT.

Then, the solver will naturally return an ITF trace containing the evaluations of `E1,...,Em` in each state `s0,...,sn` (the values of `v1,...,vm`).


## Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

TBD
