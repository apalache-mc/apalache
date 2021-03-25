# Principles of Symbolic Model Checking with Apalache

In order to take advantage of Apalache's symbolic model checking, there are a
few principles one must bear in mind when writing TLA.

<a name="assignments"></a>
<a name="symbolicTransitions"></a>
## Assignments and symbolic transitions

Let us go back to the example [`test/tla/y2k.tla`](https://github.com/informalsystems/apalache/blob/unstable/test/tla/y2k.tla) and
run `apalache` against [`test/tla/y2k_override.tla`](https://github.com/informalsystems/apalache/blob/unstable/test/tla/y2k_override.tla):

```console
$ apalache check y2k_override.tla
```

 We can check the detailed output of the `TransitionFinderPass` in the file
`x/<timestamp>/out-transition.tla`, where `<timestamp>` looks like
`09.03-10.03.2020-508266549191958257`:

```tla
----- MODULE y2k_override -----
VARIABLE year
VARIABLE hasLicense
ASSUME(80 \in 0 .. 99)
ASSUME(18 \in 1 .. 99)

Init$0 == year' := 80 /\ hasLicense' := FALSE
Next$0 == year' := ((year + 1) % 100) /\ (hasLicense' := hasLicense)
Next$1 == year - 80 >= 18 /\ hasLicense' := TRUE /\ (year' := year)
===============
```

As you can see, the model checker did two things:

1. It has translated several expressions that look like `x' = e` into `x' := e`.
   For instance, you can see `year' := 80` and `hasLicense' := FALSE` in
   `Init$0`. We call these expressions **assignments**.
1. It has factored the operator `Next` into two operators `Next$0` and `Next$1`.
   We call these operators **symbolic transitions**.

Pure TLA+ does not have the notions of assignments and symbolic
transitions.  However, TLC sometimes treats expressions `x' = e` and `x' \in S`
as if they were assigning a value to the variable `x'`. TLC does so
dynamically, during the breadth-first search. Apalache looks statically for assignments
among the expressions `x' = e` and `x' \in S`.

When factoring out operators into symbolic transitions, Apalache splits the
action operators `Init` and `Next` into disjunctions (e.g., `A_0 \/ ... \/ A_n`),
represented in the concrete syntax as a sequence of operator definitions of the
form

``` tla
A$0 == ...
...
A$n == ...
```

The main contract between the assignments and symbolic transitions is as
follows:

> For every variable `x` declared with `VARIABLE`, there is exactly one
> assignment of the form `x' := e` in every symbolic transition `A_n`.

If Apalache cannot find expressions with the above properties, it fails.
Consider the example
[`test/tla/Assignments20200309.tla`](https://github.com/informalsystems/apalache/blob/unstable/test/tla/Assignments20200309.tla):

```tla
----- MODULE Assignments20200309 -----
VARIABLE a
\* this specification fails, as it has no expression
\* that can be treated as an assignment
Init == TRUE
Next == a' = a
Inv == FALSE
===============
```

Running the checker with

```bash
apalache check Assignments20200309.tla
```

Apalache reports an error as follows:

```console
...
PASS #6: TransitionFinderPass                                     I@09:39:33.527
To understand the error, check the manual:
[https://apalache.informal.systems/docs/apalache/assignments.html]
Assignment error: Failed to find assignments and symbolic transitions in InitPrimed E@09:39:33.676
It took me 0 days  0 hours  0 min  1 sec                          I@09:39:33.678
Total time: 1.88 sec                                              I@09:39:33.678
EXITCODE: ERROR (99)
```

This error is cryptic. It does not indicate which parts of the specification
have caused the problem. In the future, we will add better diagnostic in the
assignment finder, see [the open
issue](https://github.com/informalsystems/apalache/issues/111). Our current approach is
to debug assignments by running TLC first. If running TLC takes too long, you
may try to comment out parts of the specification to find the problematic
action. Although this is tedious, it allows one to find missing assignments
rather quickly.

If you are interested in the technique for finding the assignments and symbolic
transitions implemented in Apalache, check our [paper at
ABZ'18](http://forsyte.at/wp-content/uploads/abz2018_full.pdf).  The [journal
version](http://dx.doi.org/https://doi.org/10.1016/j.scico.2019.102361) is
unfortunately behind the Elsevier paywall, which will be lifted after the
two-year embargo period.

<a name="types"></a>
## Type annotations

**NOTE 1**: [Jure Kukovec](https://forsyte.at/people/kukovec/) is developing
a completely automatic type inference engine. As soon as it is ready, type
annotations will no longer be required. Until that happy day, refer to [type
annotations](types-and-annotations.md).

**NOTE 2**: We are currently working on a better syntax for type annotations
and a better type checker. Hence, the syntax will change in the future.

Apalache requires two kinds of type annotations:
- type annotations for empty sets and sequences, and
- type annotations for records and sets of records.

### Empty sets and sequences

Consider the following example [`NeedForTypes.tla`](https://github.com/informalsystems/apalache/blob/unstable/test/tla/NeedForTypes.tla):

```tla
{{#include ../../../test/tla/NeedForTypes.tla}}
```

While this example is perfectly fine for TLC, Apalache has to assign types to
the variables, in order to construct SMT constraints. In some cases, Apalache
can infer types completely automatically, e.g., as in the `y2k` example (see
[the example](./example.md)). However, if you run `apalache check
--cinit=ConstInit NeedForTypes.tla`, the tool will complain:

```
Step 0, level 0: checking if 1 transition(s) are enabled and violate the invariant I@15:17:14.313
Step 0, level 1: collecting 1 enabled transition(s)               I@15:17:14.360
Step 1, level 1: checking if 2 transition(s) are enabled and violate the invariant I@15:17:14.374
NeedForTypes.tla:18:8-18:16, =(...), type error: Expected equal types: FinSet[Int] and FinSet[Unknown] E@15:17:14.379
The outcome is: Error                                             I@15:17:14.388
```

In a somewhat obfuscated way, Apalache tells us the following. It has inferred
that `Left` is a set of integers, that is, `FinSet[Int]`. First, it found that
`InSet` is a set of integers, by applying `ConstInit`. Second, as `Left = InSet`
in `Init`, it inferred that `Left` is also a set of integers. Third, when
applying `Next`, it processed `{}`, which is an empty set of any kind of
objects. Hence, `{}` was assigned the type `FinSet[Unknown]`, that is, a set of
some type. Finally, it found the expression `Left = {}`, and here the type
checker has failed.

To help the type checker, we have to introduce a few type annotations. But
before doing that, we introduce the notation for type annotations in the
specification.

#### Syntax for type annotations

Apalache reads any expression formed with the `<:` operator as an annotation of
the value of the left hand side with the type on the right. E.g.,

```tla
v <: T
```

means "value `v` has type `T`".

However, other tools (such as TLC and TLAPS) have no support for these
annotations. To tell them to ignore type annotations, we maintain the convention
that any file using Apalache type annotations begins with the following definition:

```tla
v <: T == v
```

With this in place, Apalache can parse out the type annotations in the rest of
the file, but other tools are told to simply read any occurrence of `v <: T` as
`v`, effectively erasing the type ascription.

Now we can help the type checker by rewriting the condition in `Next` as follows:

#### Example of using type annotations

```tla
Next ==
    IF Left = {} <: {Int}
    THEN ...
    ELSE ...
```

Now the type checker treats the expression `{}` as a set of integers. However,
it complains about another line:

```
Step 0, level 0: checking if 1 transition(s) are enabled and violate the invariant I@15:43:35.932
Step 0, level 1: collecting 1 enabled transition(s)               I@15:43:35.977
Step 1, level 1: checking if 2 transition(s) are enabled and violate the invariant I@15:43:35.992
NeedForTypes.tla:23:24-23:40, x$1, type error: Expected type Unknown, found Int E@15:43:36.012
NeedForTypes.tla:23:24-23:40, Append(...), type error: Expected a type, found: None E@15:43:36.018
NeedForTypes.tla:23:11-24:31, /\(...), type error: Expected a Boolean, found: None E@15:43:36.020
The outcome is: Error
```

Here the type checker stumbles upon the sequence operator `Append(OutSeq, x)`
and complains about the type mismatch. Similar to `{}`, it has treated
the expression `<< >>` as a sequence of an unknown type. (In case of `<<1, 2>>`
it would be even worse, as the type checker would not know, whether `<<1, 2>>`
should be treated as a sequence or a tuple). Again, we help the type checker
by modifying `Init` as follows:

```tla
Init ==
    /\ OutSeq = << >> <: Seq(Int)
    ...
```

Having these two annotations, the type checker stops complaining. You can find
the annotated specification in
[`test/tla/NeedForTypesWithTypes.tla`](https://github.com/informalsystems/apalache/blob/unstable/test/tla/NeedForTypesWithTypes.tla).

### Records and sets of records

Consider the following example in
[`test/tla/Handshake.tla`](https://github.com/informalsystems/apalache/blob/unstable/test/tla/Handshake.tla):

```tla
------------------------ MODULE Handshake ------------------------
(**
 * A TCP-like handshake protocol:
 * https://en.wikipedia.org/wiki/Transmission_Control_Protocol#Connection_establishment
 *
 * Igor Konnov, 2020
 *)
EXTENDS Integers

VARIABLES msgs,     \* the set of all messages
          iseqno,   \* Initiator's sequence number
          rseqno,   \* Receiver's sequence number
          istate,   \* Initiator's state
          rstate    \* Receiver's state

a <: b == a

Init ==
    /\ msgs = {}
    /\ iseqno = 0
    /\ rseqno = 0
    /\ istate = "INIT"
    /\ rstate = "LISTEN"

SendSyn ==
    /\ istate = "INIT"
    /\ \E no \in Nat:
        /\ msgs' = msgs \union {[syn |-> TRUE,
                                 ack |-> FALSE, seqno |-> no]}
        /\ iseqno' = no + 1
        /\ istate' = "SYN-SENT"
        /\ UNCHANGED <<rseqno, rstate>>

SendSynAck ==
    /\ rstate = "LISTEN"
    /\ \E seqno, ackno \in Nat:
        /\ [syn |-> TRUE, ack |-> FALSE, seqno |-> seqno] \in msgs
        /\ msgs' = msgs \union {[syn |-> TRUE, ack |-> TRUE,
                                 seqno |-> seqno + 1,
                                 ackno |-> ackno]}
        /\ rseqno' = ackno + 1
        /\ rstate' = "SYN-RECEIVED"
        /\ UNCHANGED <<iseqno, istate>>

SendAck ==
    /\ istate = "SYN-SENT"
    /\ \E ackno \in Nat:
        /\ [syn |-> TRUE, ack |-> TRUE,
            seqno |-> iseqno, ackno |-> ackno] \in msgs
        /\ istate' = "ESTABLISHED"
        /\ msgs' = msgs \union {[syn |-> FALSE, ack |-> TRUE,
                                 seqno |-> iseqno,
                                 ackno |-> ackno + 1]}
        /\ UNCHANGED <<iseqno, rseqno, rstate>>

RcvAck ==
    /\ rstate = "SYN-RECEIVED"
    /\ \E seqno \in Nat:
        /\ ([syn |-> FALSE, ack |-> TRUE,
             seqno |-> seqno, ackno |-> rseqno]) \in msgs
        /\ rstate' = "ESTABLISHED"
        /\ UNCHANGED <<msgs, iseqno, rseqno, istate>>


Next == SendSyn \/ SendSynAck \/ SendAck \/ RcvAck

Inv == (rstate = "ESTABLISHED" => istate = "ESTABLISHED")
======================================================================
```

As we have seen before, the type checker complains about the set `msgs`,
which is initialized as `{}`. So we have to specify the type of `{}`. But which
type shall we use for the empty set?

In our example, the set `msgs` may contain records of three kinds:
- a **SYN** request that is modeled as a record
    `[ack |-> FALSE, syn |-> TRUE, seqno |-> i]` for some number `i`,
- a **SYN-ACK** reply that is modeled as a record
    `[ack |-> TRUE, syn |-> TRUE, seqno |-> i, ackno |-> j]`
    for some numbers `i` and `j`,
- an **ACK** reply that is modeled as a record
    `[ack |-> TRUE, syn |-> FALSE, seqno |-> i, ackno |-> j]`
    for some numbers `i` and `j`.

From the perspective of the type checker, the three records shown above have
three different types. Although we would love to reject this example as an
ill-typed one, mixing records of different types is a widely-accepted idiom in
TLA+, for instance, see [Lamport's specification of
Paxos](https://github.com/tlaplus/Examples/blob/master/specifications/Paxos/Paxos.tla).
Think of records as of C unions, rather than C structs!

To help the type checker, we first introduce a handy operator for the type that
contains the fields of the three records:

```tla
MT == [syn |-> BOOLEAN, ack |-> BOOLEAN, seqno |-> Int, ackno |-> Int]
```

Then we add annotations as follows:

```tla
Init ==
  /\ msgs = {} <: {MT}
    ...

SendSyn ==
  ...
  /\ \E no \in Nat:
    /\ msgs' = msgs \union {[syn |-> TRUE, ack |-> FALSE, seqno |-> no] <: MT}
  ...

SendSynAck ==
  ...
  /\ \E seqno, ackno \in Nat:
    /\ ([syn |-> TRUE, ack |-> FALSE, seqno |-> seqno] <: MT) \in msgs
    ...

SendAck ==
  ...
  /\ \E ackno \in Nat:
    ...
```

As you can see, we have to annotate only those records that do not have all
four fields of `MT`. As soon as we have added the annotations, the type checker
stopped complaining and let the model checker to run. The annotated code can be
found in
[`test/tla/HandshakeWithTypes.tla`](https://github.com/informalsystems/apalache/blob/unstable/test/tla/HandshakeWithTypes.tla).

Type annotations can be also applied to sets of records. For example:

```tla
[syn |-> BOOLEAN, ack |-> BOOLEAN, seqno |-> Int] <: {MT}
```

You can find more details on the simple type inference algorithm and the type
annotations in [type annotations](types-and-annotations.md).

### Naturals

If you look carefully at the [type annotations](types-and-annotations.md), you
will find that there is no designated type for naturals. Indeed, one can just
use the type `Int`, whenever a natural number is required. If we introduced a
special type for naturals, that would cause a lot of confusion for the type
checker. What would be the type of the literal `42`? That depends on, whether
you extend `Naturals` or `Integers`. And if you extend `Naturals` and later
somebody else extends your module and also `Integers`, should be the type
of `42` be an integer?

Apalache still allows you to extend `Naturals`. However, it will treat all
number-like literals as integers. This is consistent with the view that the naturals are
a subset of the integers, and the integers are a subset of the reals.  Classically, one
would not define subtraction for naturals. However, the module `Naturals`
defines binary minus, which can easily drive a variable outside of `Nat`. For
instance, see the following example:

```tla
----------------------------- MODULE NatCounter ------------------------
EXTENDS Naturals

VARIABLE x

Init == x = 3

\* a natural counter can go below zero, and this is expected behavior
Next == x' = x - 1

Inv == x >= 0
========================================================================
```

Given that you will need the value `Int` for a type annotation, it probably
does not make a lot of sense to extend `Naturals` in your own specifications,
as you will have to extend `Integers` for the type annotation too.  We are
currently working on a different kind of type annotations, which would not
require `Int`.


<a name="recursion"></a>
## Recursive operators and functions

<a name="rec-op"></a>
### Recursive operators

In the preprocessing phase, Apalache replaces every application of a user
operator with its body. We call this process "operator inlining".
This cannot be done for recursive operators, for two reasons:

 1. A recursive operator may be non-terminating (although a non-terminating
    operator is useless in TLA+);

 1. A terminating call to an operator may take an unpredicted number of iterations.

However, in practice, when one fixes specification parameters (that is,
`CONSTANTS`), it is usually easy to find a bound on the number of operator
iterations. For instance, consider the following specification:

```tla
--------- MODULE Rec6 -----------------
CONSTANTS N
VARIABLES set, count

RECURSIVE Sum(_)

Sum(S) ==
  IF S = {}
  THEN 0
  ELSE LET x == CHOOSE x \in S: TRUE IN
    x + Sum(S \ {x})

Init ==
  /\ set = {}
  /\ count = 0

Next ==
  \E x \in (1..N) \ set:
    /\ count' = count + x
    /\ set' = set \union {x}

Inv == count = Sum(set)
=======================================
```

It is clear that the expression `Sum(S)` requires the number of iterations that
is equal to `Cardinality(S) + 1`. Moreover, the expression `set \subseteq
1..N` is an invariant, and thus every call `Sum(set)` requires up to `N+1`
iterations.

When we can find an upper bound on the number of iterations, Apalache can
unroll the recursive operator up to this bound. To this end, we define two
additional operators. For instance:

```tla
--------- MC_Rec6 ----------
VARIABLES set, count

INSTANCE Rec6 WITH N <- 3

UNROLL_TIMES_Sum == 4
UNROLL_DEFAULT_Sum == 0
============================
```

In this case, Apalache unrolls every call to `Sum` exactly `UNROLL_TIMES_Sum`
times, that is, four times. On the default branch, Apalache places
`UNROLL_DEFAULT_Sum`, that is, 0.

All recursively defined operators should follow this convention where, for every such operator `Oper`, the user defines both `UNROLL_TIMES_Oper`, which expands to a positive integer value, and `UNROLL_DEFAULT_Oper`, which expands to some default value `Oper(args*)` should take, if the computation would require more than `UNROLL_TIMES_Oper` recursive calls.
At present, we only support literals (e.g. `4`) or primitive arithmetic expressions (e.g. `2 + 2`) in the body of `UNROLL_TIMES_Oper`.

<a name="rec-fun"></a>

#### Recursive functions

Apalache offers limited support for recursive functions. However, read the
warning below on why you should not use recursive functions. The restrictions
are as follows:

 1. Apalache supports recursive functions that return an integer or a Boolean.

 1. As Apalache's simple type checker is not able to find the type of a
recursive function, all uses of a recursive function should come with a type
annotation.

 1. As in TLC, the function domain must be a finite set.

The example below shows a recursive function that computes the factorial of `n`.


```tla
------------------------------ MODULE Rec8 ------------------------------------
EXTENDS Integers

VARIABLES n, factSpec, factComp

\* the syntax for type annotations
a <: b == a

\* the type of the factorial function
FactT == [Int -> Int]

(*
 Defining a recursive function on a finite domain. Although it is rather
 unnatural to define factorial on a finite set, both Apalache and TLC
 require finite domains. As is usual for function application, the result
 of the application is not defined on the elements outside of the function
 domain.
 *)
Fact[k \in 1..20] ==
    IF k <= 1
    THEN 1
    ELSE k * (Fact <: FactT)[k - 1]

Init ==
    /\ n = 1
    /\ factSpec = Fact[n]
    /\ factComp = 1

Next ==
    /\ n' = n + 1
    /\ factSpec' = Fact[n']
    /\ factComp' = n' * factComp

Inv ==
    factComp = factSpec
===============================================================================
```

Check other examples in
[`test/tla`](https://github.com/informalsystems/apalache/tree/unstable/test/tla) that
start with the prefix `Rec`.

**Why you should avoid recursive functions.** Sometimes, recursive functions
concisely describe the function that you need. The nice examples are the
factorial function (see above) and Fibonacci numbers (see
[Rec3](https://github.com/informalsystems/apalache/blob/unstable/test/tla/Rec3.tla)).
However, when you define a recursive function over sets, the complexity gets
ugly really fast.

Consider the example
[Rec9](https://github.com/informalsystems/apalache/blob/unstable/test/tla/Rec9.tla),
which computes set cardinality. Here is a fragment of the spec:

```tla
{{#include ../../../test/tla/Rec9.tla:19:32}}
```

Since we cannot fix the order, in which the set elements are evaluated, we
define function `Card` over `SUBSET NUMS`, that is, all possible subsets of
`NUMS`. Apalache translates the function in a quantifier-free theory of SMT.
Hence, in this case, Apalache expands `SUBSET NUMS`, so it introduces
`2^|NUMS|` sets! Further, Apalache writes down the SMT constraints for the
domain of `Card`. As a result, it produces `NUMS * 2^|NUMS|` constraints.
As you can see, recursive functions over sets explode quite fast.

It is usually a good idea to use recursive operators over sets rather than
recursive functions. The downside is that you have to provide an upper bound on
the number of the operator iterations. The upside is that recursive operators
are usually unrolled more efficiently. (If they contain only constant
expressions, they are even computed by the translator!) For instance, set
cardinality does not require `2^|NUMS|` constraints, when using a recursive
operator.
