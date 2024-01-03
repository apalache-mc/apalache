# ADR-16: ReTLA - Relational TLA

| author       | revision  |
| ------------ | --------: |
| Jure Kukovec | 1         |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

<!-- Statement to summarize, following the following formula: -->
<!--
  In the context of (use case)\
facing (concern)\
we decided for (option)\
to achieve (quality)\
accepting (downside).\
-->

We propose introducing support for a severely restricted fragment of TLA+, named Relational TLA (reTLA for short), which covers uninterpreted first-order logic. The simplicity of this fragment should allow Apalache to use a more straightforward encoding, both in SMT, as well as potentially in languages suited for alternative backend solvers. 

Running Apalache with this encoding would skip the model-checking pass and instead produce a standalone file containing all of the generated constraints, which could be consumed by other tools.

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->
Apalache currently supports almost the full suite of TLA+ operators. Consequently, the standard encoding of TLA+ into SMT is very general, and a lot of effort is spent on encoding data structures, such as sets or records, and their evolution across the states. Additionally, we need to track arenas; bookkeeping auxiliary constructions, which are a byproduct of our encoding approach, not TLA+ logic itself.

However, it is often the case that, with significant effort on the part of the specification author, expressions can be rewritten in a way that avoids using the more complex structures of TLA+. For example, consider the following snippet of a message-passing system:
```tla
CONSTANT Values
VARIABLE messages

SendT1(v) == messages \union { [ type |-> "t1", x |-> v ] }

ReadT1 == 
  \E msg \in messages:
    /\ msg.type = "t1"
    /\ F(msg.x) \* some action

Next ==
  \/ \E v \in Values: SendT1(v)
  \/ ReadT1
```

The central object is the set `messages`, which is modified at each step, and contains records. This makes it one of the more expensive expressions, in terms of the underlying SMT encodings in Apalache. However, as far as the use of `messages` goes, there is a major insight to be had: _it is not necessary to model `messages` explicitly for `ReadT1`, we only need to specify the property that certain messages of type "t1" with given payloads have been sent_. Naturally, modeling `messages` explicitly is _sufficient_ for this purpose, but if one wanted to avoid the use of sets and records, one could write the following specification instead:
```tla
CONSTANT Values
VARIABLE T1messages

SendT1(v) == [T1messages EXCEPT ![v] = TRUE]

ReadT1 ==
  \E v \in Values:
    /\ T1messages[v]
    /\ F(v) \* some action

Next ==
  \/ \E v \in Values: SendT1(v)
  \/ ReadT1
```

By encoding, for example, set membership checks as predicate evaluations, one can write some specifications in a fragment of TLA+ that avoids all complex data structures, sets-of-sets, records, sequences, and so on, and replaces them with predicates (functions).
Rewriting specifications in this way is nontrivial, and shouldn't be expected of engineers, however, should a specification author undertake such a transformation, we should be able to provide some payoff.
If we only limit ourselves to specifications in this restricted fragment (defined explicitly below), the current SMT encoding is needlessly complex. 
We can implement a specialized encoding, which does not use arena logic of any kind, but is much more direct and even lends itself well to multiple kinds of solvers (e.g. IVy or VMT, in addition to standard SMT).

## Options

<!-- Communicate the options considered.
     This records evidence of our circumspection and documents the various alternatives
     considered but not adopted.
-->
1. Reuse most of the existing implementation and encoding, with a modified language watchdog, then output an SMT file from the context, instead of solving.
    - Pros:

      - Little work

    - Cons:

      - Locked to the SMT format
      - Unnecessary additional SMT constraints produced

1. Write custom rewriting rules that generate constraints symbolically
    - Pros:

      - Fewer constraints
      - Higher level of abstraction
      - Can support multiple output formats

    - Cons:

      - More work


## Solution

<!-- Communicates what solution was decided, and it is expected to solve the
     problem. -->

We propose option (2), and give the following categorization of the reTLA fragment:

  - Boolean, integer and uninterpreted literals (including strings)
  - Restricted sets: 
    - `Int`, `Nat` or `BOOLEAN`, or 
    - `CONSTANT`-declared and has a type `Set(T)`, for some uninterpreted type `T`, or
  - Boolean operators (`/\, \/, =>, <=>, ~`)
  - Quantified expressions (`\E x \in S: P, \A x \in S: P`), on the condition that `P` is in reTLA and `S` is a restricted set.
  - Functions:
    - Definitions (`[x1 \in S1, ..., xn \in Sn |-> e]`), on the condition that:
      - `e` is in reTLA and has an `Int`, `Bool` or uninterpreted type
      - All `Si` are restricted sets.
    - Updates (`[f EXCEPT ![x] = y]`), if `y` is in reTLA
    - Applications (`f[x]`)
  - (In)equality and assignments:
    - `a = b` and `a /= b` if both `a` and `b` are in reTLA
    - `x' = v` if `x` is a `VARIABLE` and `v` is in reTLA
  - Control flow:
    - `IF p THEN a ELSE b` if `p,a,b` are all in reTLA

In potential future versions we are likely to also support: 
  - Standard integer operators (`+, -, u-, *, %, <, >, <=, >=`)
  - ranges `a..b`, where both `a` and `b` are in reTLA.
  - Tuples

## Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

Reserved for the future.
