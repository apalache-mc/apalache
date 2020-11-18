# Idiom 1: Update state variables with assignments

## Description

The idiom "[Keep state variables to the
minimum](000keep-minimum-state-variables.md)" tells us to store the minimum
necessary state variables. By following this idiom, we develop
the specification by writing constraints over the primed variables.

TLA+ comes with a great freedom of expressing constraints over variables.
While we love TLA+ for that freedom, we believe that constraints over primed
variables are sometimes confusing.
TLA+ uses the same glyph, `=` for three separate purposes: assignment, asserting equality, and binding variables. But these are very different operations and have different semantics.
### Issue 1

**tl;dr:** Use `:=` (supplied by the `Apalache.tla` module) instead of `=` for assignment.

Consider the expression:

```tla
  x' = x + 1
```

It is all clear here. The value of `x` in the next states (there may be many)
is equal to `val(x)+1`, where `val(x)` is the value of `x` in the current
state.

Wait. Is it clear? What if that expression was just the first line of the following
expression:

```tla
  x' = x + 1
    => x' = 3
```

This says, "if `x'` is equal to `x + 1`, then assign `x'` to `3` in the next state", which
implies that `x'` may receive a value from the set:

```tla
  { 3 } \union { y \in Int: y /= val(x) + 1 }
```

But maybe the author of that specification just made a typo and never
meant to put the implication `=>` in the first place. Actually, the intended
specification looks like follows:

```tla
  x' = x + 1
    \/ x' = 3
```

We believe that it is helpful to label the expressions that intend to denote the
values of the state variables in the next state. Apalache introduces the infix
operator `:=` in the module `Apalache.tla` for that purpose:

```tla
  x' := x + 1
    \/ x' := 3
```

Hence, it would be obvious in our motivating example that the author made a typo:

```tla  
  x' := x + 1
    => x' := 3
```
because the assignment `x' := x + 1` does not express a boolean value
and so cannot be the antecedent of the conditional.
### Issue 2
**tl;dr:** Use existential variables with the `:=` operator for non-deterministic assignment.

Another common use of primed variables is to select the next value of a variable
from a set:

```tla
  x' \in { 1, 2, 3 }
```

This expression can be rewritten as an equivalent one:

```tla
  \E y \in { 1, 2, 3 }:
    x' = y
```

Which one to choose? The first one is more concise. The second one highlights
the important effect, namely, non-deterministic choice of the next value of `x`.
When combined with the operator `:=`, the effect of non-deterministic choice is
clearly visible:

```tla
  \E y \in { 1, 2, 3 }:
    x' := y
```

In fact, every constraint over primes can be translated into the existential form.
For instance, consider the expression:

```tla
  x' * x' = 4
```

It can be written as:

```tla
  \E y \in Int:
    /\ y * y = 4
    /\ x' := y
```

## Advantages

 - The reader clearly sees the writer's intention about the updates
   to the primed variables.

 - Non-determinism is clearly isolated in existential choice: `\E y \in S: x' := y`.
   If there is no existential choice, the assignment is deterministic.

 - When the existential form is used, the range of the values is clearly indicated.
   This is in contrast to the negated form such as: `~(x' = 10)`.

 - TLC treats the expressions of the form `x' = e` and `x' \in S` as assignments,
   as long as `x'` is not bound to a value. 

 - Apalache uses assignments to decompose the specification into smaller pieces.
   Although Apalache tries to find assignments automatically, it often has to choose
   from several expressions, some of them may be more complex than the others. By using
   the `:=` operator, Apalache gets unambiguous instructions about when assignment is taking
   place

## Disadvantages

  - Replacing `x' \in S` with `\E y \in S: x' := y` makes the specification a bit larger.

## Example

The following example [deliver.tla](./example/deliver.tla) demonstrates how
one can clearly mark assignments using the `:=` operator.

```tla
------------------------------ MODULE deliver ----------------------------------
(*
 * A simple specification of two processes in the network: sender and receiver.
 * The sender sends messages in sequence. The receiver may receive the sent
 * messages out of order, but delivers them to the client in order.
 *
 * Igor Konnov, 2020
 *)
EXTENDS Integers, Apalache

VARIABLES
    sentSeqNo,      \* the sequence number of the next message to be sent
    sent,           \* the messages that are sent by the sender
    received,       \* the messages that are received by the receiver
    deliveredSeqNo  \* the sequence number of the last delivered message
(* We assign to the unprimed state variables to set their initial values. *)
Init ==
    /\ sentSeqNo := 0
    /\ sent := {}
    /\ received := {}
    /\ deliveredSeqNo := -1

(* Subsequent assignments are all to primed variables, designating changed values
   after state transition. *)
Send ==
    /\ sent' := sent \union {sentSeqNo}
    /\ sentSeqNo' := sentSeqNo + 1
    /\ UNCHANGED <<received, deliveredSeqNo>>

Receive ==
    (* We make the nonderministic assignment explicit, by use of existential quantification *)
    /\ \E msgs \in SUBSET (sent \ received):
        received' := received \union msgs
    /\ UNCHANGED <<sentSeqNo, sent, deliveredSeqNo>>

Deliver ==
    /\ (deliveredSeqNo + 1) \in received
    /\ deliveredSeqNo' := deliveredSeqNo + 1
        \* deliver the message with the sequence number deliveredSeqNo'
    /\ UNCHANGED <<sentSeqNo, sent, received>>

Next ==
    \/ Send
    \/ Receive
    \/ Deliver

Inv ==
    (deliveredSeqNo >= 0) => deliveredSeqNo \in sent
================================================================================
```
