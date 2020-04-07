# Apalache manual

**Version 0.7.0** :fireworks:

**Authors: Igor Konnov, Jure Kukovec, and Andrey Kuprianov**

**Contact: {igor,andrey} at informal.systems, jkukovec at forsyte.at**

# Introduction

Apalache is a symbolic model checker for [TLA+](https://lamport.azurewebsites.net/tla/tla.html). (*Still looking for a better tool name.*) Our model checker is a recent alternative to [TLC](https://lamport.azurewebsites.net/tla/tools.html?unhideBut=hide-tlc&unhideDiv=tlc).
Whereas TLC enumerates states that are produced by behaviors of a TLA+ specification, Apalache translates the verification problem to a set of logical constraints. These constraints are solved by an [SMT solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories), for instance, by [Microsoft Z3](https://github.com/Z3Prover/z3). That is, Apalache is operating in terms of formulas (i.e., _symbolic_), not enumerating states one by one (i.e., _state enumeration_).

Apalache is working under the following assumptions:

 1. As in TLC, all specification parameters are fixed and finite, i.e., the system state is initialized with integers, finite sets, and functions of finite domains and co-domains.

 2. As in TLC, all data structures evaluated during an execution are finite, e.g., a system specification cannot operate on the set of all integers.

 3. Only finite executions of bounded length are analyzed.


# Table of Contents

 1. [Shall I use Apalache or TLC?](#apalacheOrTlc)
 1. [System requirements](#sysreq)
 1. [Installation](#installation)
 1. [An example of a TLA+ specification](#example)
 1. [Setting up specification parameters](#parameters)
 1. [Running the tool](#running)
 1. [Understanding assignments](#assignments)
 1. [Type annotations](#types)
 1. [Recursive operators and functions](#recursion)
 1. [Five minutes of theory](#theory5)
 1. [Supported language features](#features)


<a name="apalacheOrTlc"></a>

# 1. Shall I use Apalache or TLC?

We recommend to start with TLC. It is mature, well-documented, and well-integrated into TLA+ Toolbox. Once you have debugged your TLA+ specification, and TLC is still producing too many reachable states, switch to Apalache. We are using this approach at [Informal Systems](https://informal.systems/).

<a name="sysreq"></a>

# 2. System requirements

Every commit to [master](https://github.com/konnov/apalache) and
[unstable](https://github.com/konnov/apalache/tree/unstable) is built with
[Travis CI](https://travis-ci.org/konnov/apalache) on MacOS (xcode9.3 and JDK
1.8.0) and Linux (OpenJDK8). If you like to run Apalache in Windows, use a
docker image. Check the [Docker
manual](https://docs.docker.com/docker-for-windows/) and the section on [Using
a docker image](#useDocker).

As Apalache is using Microsoft Z3 as a backend SMT solver, the required memory
largely depends on Z3. We recommend to allocate at least 4GB of memory for the
tool.

<a name="installation"></a>

# 3. Installation

There are two ways to run Apalache: (1) Download and run a docker image, or (2)
Build Apalache from sources and run the compiled package. If you just like to
try the tool, we recommend to use the docker image. If you like to run the tool
on daily basis or to contribute to the project, we recommend to build the project
from the sources. In the following, we write `$APALACHE_HOME` to refer to the
directory, where Apalache is cloned.

<a name="useDocker"></a>   

## 3.1. Using a docker image

**Starting with release 0.6.0, we will publish Docker images for every release** :sunglasses:

To get the latest Apalache image, issue the command:

```
docker pull apalache/mc
```

**Running the docker image**. To run an Apalache image, issue the command:

```bash
$ docker run --rm -v <your-spec-directory>:/var/apalache apalache/mc <args>
```

The following docker parameters are used:
- `--rm` to remove the container on exit
- `-v <your-spec-directory>:/var/apalache` bind-mounts `<your-spec-directory>` into
  `/var/apalache` in the container. **This is necessary for
  Apalache to access your specification and the modules it
  extends.**
  From the user perspective, it works as if Apalache was
  executing in `<your-spec-directory>`.
  In particular the tool logs are written in that directory.

  When using SELinux, you might have to use the modified form of `-v` option:
    `-v <your-spec-directory>:/var/apalache:z`
- `apalache/mc` is the APALACHE docker image name. By default, the `latest` stable
  version is used; you can also refer to a specific tool version, e.g., `apalache/mc:0.6.0`
- `<args>` are the tool arguments as described in
  [Running the tool](#running).

**Setting an alias.**
If you are running Apalache on Linux :penguin: or MacOS :green_apple:,
you can set the handy alias,
which runs Apalache in docker while sharing the working directory:

```bash
$ alias apalache="docker run --rm -v `pwd`:/var/apalache apalache/mc"
```

**Building an image**. For an end user there is no need to build an Apalache
image. If you like to produce a modified docker image,
take into account that it will take about 30 minutes for the image
to get built, due to compilation times of Microsoft Z3.
To build a docker image of Apalache, issue the following command
in `$APALACHE_HOME`:

```bash
$ docker image build -t apalache:0.6.0 .
```


## 3.2.  Building from sources

1. Install `git`.
2. Clone the git repository: `git clone https://github.com/konnov/apalache.git`
3. Install OpenJDK8 or
[Zulu JDK8](https://www.azul.com/downloads/zulu-community/?&architecture=x86-64-bit&package=jdk).
**You have to install version 8, otherwise Scala will not compile! See
[see compatibility
table](https://docs.scala-lang.org/overviews/jdk-compatibility/overview.html).**

4. Install [Apache Maven](https://maven.apache.org/). For instance,
   when using Debian Linux or Ubuntu: `sudo apt-get install maven`
5. Run `make`. This command will install Microsoft Z3, compile Apalache
   and assemble the package

<a name="example"></a>

# 4. An example of a TLA+ specification

To illustrate the features of Apalache, we are using the following TLA+ specification,
which can be found in [`test/tla/y2k.tla`](../test/tla/y2k.tla):

```tla
-------------------------------- MODULE y2k --------------------------------
(*
 * A simple specification of a year counter that is subject to the Y2K problem.
 * In this specification, a registration office keeps records of birthdays and
 * issues driver's licenses. As usual, a person may get a license, if they
 * reached a certain age, e.g., age of 18. The software engineers never thought
 * of their program being used until the next century, so they stored the year
 * of birth using only two digits (who would blame them, the magnetic tapes
 * were expensive!). The new millennium came with new bugs.
 *
 * This is a made up example, not reflecting any real code.
 * To learn more about Y2K, check: https://en.wikipedia.org/wiki/Year_2000_problem
 *
 * Igor Konnov, January 2020
 *)
EXTENDS Integers

CONSTANT BIRTH_YEAR,    \* the year to start with, between 0 and 99
         LICENSE_AGE    \* the minimum age to obtain a license

ASSUME(BIRTH_YEAR \in 0..99)              
ASSUME(LICENSE_AGE \in 1..99)              

VARIABLE year, hasLicense

Age == year - BIRTH_YEAR

Init ==
    /\ year = BIRTH_YEAR
    /\ hasLicense = FALSE

NewYear ==
    /\ year' = (year + 1) % 100 \* the programmers decided to use two digits
    /\ UNCHANGED hasLicense

IssueLicense ==
    /\ Age >= LICENSE_AGE
    /\ hasLicense' = TRUE
    /\ UNCHANGED year

Next ==
    \/ NewYear
    \/ IssueLicense

\* The somewhat "obvious" invariant, which is violated    
Safety ==
    hasLicense => (Age >= LICENSE_AGE)

\* This is probably the only invariant we can formulate, usually, it is called TypeOK    
Inv ==
    /\ year \in 0..99
    /\ hasLicense \in BOOLEAN
=============================================================================
```

<a name="parameters"></a>

# 5. Setting up specification parameters

Similar to TLC, Apalache requires the specification parameters to be restricted
to finite values. In contrast to TLC, there is a way to initialize parameters
by writing a symbolic constraint, see [Section 5.3](#ConstInit).

## 5.1. Using INSTANCE

You can set the specification parameters, using the standard `INSTANCE`
expression of TLA+. For instance, below is the example
[`test/tla/y2k_instance.tla`](../test/tla/y2k_instance.tla), which instantiates
`y2k.tla`:

```tla
---------------------------- MODULE y2k_instance ----------------------------
VARIABLE year, hasLicense

INSTANCE y2k WITH BIRTH_YEAR <- 80, LICENSE_AGE <- 18
=============================================================================
```

The downside of this approach is that you have to declare the variables of the
extended specification.

## 5.2. Convention over configuration

```tla
---------------------------- MODULE y2k_override ----------------------------
EXTENDS y2k

OVERRIDE_BIRTH_YEAR == 80
OVERRIDE_LICENSE_AGE == 18
=============================================================================
```

<a name="ConstInit"></a>

## 5.3. ConstInit predicate

This approach is similar to the ``Init`` operator, but applied to the
constants. We define a special operator, e.g., called ``ConstInit``. For
instance, below is the example
[`test/tla/y2k_cinit.tla`](../test/tla/y2k_cinit.tla):

```tla
---------------------------- MODULE y2k_cinit ----------------------------
EXTENDS y2k

ConstInit ==
    /\ BIRTH_YEAR \in 0..99
    /\ LICENSE_AGE \in 10..99
=============================================================================
```

To use `ConstInit`, pass it as the argument to `apalache`. For instance, for
`y2k_cinit`, we would run the model checker as follows:

```tla
$ cd $APALACHE_HOME/test/tla
$ apalache check --inv=Safety \
  --length=20 --cinit=ConstInit y2k_cinit.tla
```

**Parameterized initialization**. As a bonus of this approach, Apalache allows
one to check a specification over a bounded set of parameters.  For example:

```tla
CONSTANT N, Values

ConstInit ==
  /\ N \in 3..10
  /\ Values \in SUBSET 0..4
  /\ Values /= {}
```

The model checker will try the instances for all the combinations of
the parameters specified in ``ConstInit``, that is, in our example, it will
consider ``N \in 3..10`` and all non-empty value sets that are subsets of ``0..4``.

**Limitation**. ``ConstInit`` should be a conjunction
of such assignments and possibly of additional constraints on the
constants. For instance, you should not write `N = 10 \/ N = 20`.
However, you can write `N \in {10, 20}`.

## 5.4. TLC configuration file

*We are planning to support TLC configuration files soon*. Follow [Issue 76](https://github.com/konnov/apalache/issues/76).

# 6. Running the tool <a name="running"></a>

## 6.1. Command-line parameters

The model checker can be run as follows:

```bash
$ apalache check [--init=Init] [--cinit=ConstInit] \
    [--next=Next] [--inv=Inv] [--length=10] [--tuning=filename] myspec.tla
```

The arguments are as follows:

  * ``--init`` specifies the initialization predicate, the default name is ``Init``
  * ``--next`` specifies the transition predicate, the default name is ``Next``
  * ``--cinit`` specifies the constant initialization predicate, optional
  * ``--inv`` specifies the invariant to check, optional
  * ``--length`` specifies the upper bound on the length of the finite executions to explore
  * ``--tuning`` specifies the properties file that stores the options for
  [fine tuning](tuning.md)

If you like to check an inductive invariant ``Inv``, you can run two commands:   

```bash
$ apalache check --init=Inv --inv=Inv --length=1 myspec.tla
```

and

```bash
$ apalache check --init=Init --inv=Inv --length=0 myspec.tla
```

Make sure that ``Inv`` contains necessary constraints on the shape of the variables.
Usually, ``TypeOK`` as the first line of the invariant is exactly what is needed.

## 6.2. Examples

**Checking safety up to 20 steps:**

```bash
$ cd test/tla
$ apalache check --length=20 --inv=Safety y2k_override.tla
```

This command checks, whether `Safety` can be violated in 20
specification steps.

**Checking an inductive invariant:**

```bash
$ cd test/tla
$ apalache check --length=0 --init=Init --inv=Inv y2k_override.tla
$ apalache check --length=1 --init=Inv  --inv=Inv y2k_override.tla
```

The first call to apalache checks, whether the initial states
satisfy the invariant. The second call to apalache checks, whether
a single specification step satisfies the invariant, when starting
in a state that satisfies the invariant. (That is why these
invariants are called inductive.)

**Using a constant initializer:**

```bash
$ cd test/tla
apalache check --cinit=ConstInit --length=20 --inv=Safety y2k_cinit.tla
```

This command checks, whether `Safety` can be violated in 20
specification steps. The consants are initialized with the predicate `ConstInit`:

```tla
ConstInit == BIRTH_YEAR \in 0..99 /\ LICENSE_AGE \in 10..99
```

In this case, Apalache finds a safety violation, e.g., for
`BIRTH_YEAR=89` and `LICENSE_AGE=10`. A complete counterexample
is printed in `counterexample.txt`.

## 6.3. Detailed output

The tool will display only the important messages. A detailed log can be found
in `detailed.log`.

Additionally, the model checker passes produce intermediate TLA+ files are in
the run-specific directory `x/hh.mm-DD.MM.YYYY-<id>`:

  - File `out-parser.tla` is produced as a result of parsing and importing
    into Apalache TLA IR.
  - File `out-config.tla` is produced as a result of substituting CONSTANTS,
    as described in [Section 5](#parameters).
  - File `out-inline.tla` is produced as a result of inlining operator
    definitions and LET-IN definitions.
  - File `out-priming.tla` is produced as a result of replacing constants and
    variables in `ConstInit` and `Init` with their primed versions.
  - File `out-vcgen.tla` is produced as a result of extracting verification
    conditions, e.g., invariants to check.
  - File `out-prepro.tla` is produced as a result of running all preprocessing
    steps.
  - File `out-transition.tla` is produced as a result of finding assignments
    and symbolic transitions.
  - File `out-opt.tla` is produced as a result of expression optimizations.
  - File `out-analysis.tla` is produced as a result of analysis, e.g.,
    marking Skolemizable expressions and expressions to be expanded.

<a name="assignments"></a>

# 7. Understanding assignments

Let us go back to the example [`test/tla/y2k.tla`](../test/tla/y2k.tla) and
run `apalache` against [`test/tla/y2k_override.tla`](../test/tla/y2k_override.tla):

```console
$ apalache check y2k_override.tla
```

The model checker ran successfully. We can check the detailed output of the
`TransitionFinderPass` in the file `x/<timestamp>/out-transition.tla`, where
`<timestamp>` looks like `09.03-10.03.2020-508266549191958257`:

```tla
----- MODULE y2k_override -----
VARIABLE year
VARIABLE hasLicense
ASSUME(80 \in 0 .. 99)
ASSUME(18 \in 1 .. 99)

Init$0 == year' <- 80 /\ hasLicense' <- FALSE
Next$0 == year' <- ((year + 1) % 100) /\ (hasLicense' <- hasLicense)
Next$1 == year - 80 >= 18 /\ hasLicense' <- TRUE /\ (year' <- year)
===============
```

As you can see, the model checker did two things:

 1. It has translated several expressions that look like `x' = e` into `x' <- e`.
   For instance, you can see `year' <- 80` and `hasLicense' <- FALSE` in `Init$0`.
   We call these expressions **assignments**.

 1. It has replaced the operator `Next` into two operators `Next$0` and `Next$1`.
   We call these operators **symbolic transitions**.

The pure TLA+ does not have the notions of assignments and symbolic
transitions.  However, TLC sometimes treats expressions `x' = e` and `x' \in S`
as if they were assigning a value to the variable `x'`. TLC does so
dynamically, during the breadth-first search. Apalache looks statically for assignments
among the expressions `x' = e` and `x' \in S`.

Moreover, Apalache splits action operators `Init` and `Next` into disjunctions
(e.g., `A_1 \/ ... \/ A_k`). The main contract between the assignments and
symbolic transitions is as follows:

> For every variable `x` declared with `VARIABLE`, there is exactly one assignment
of the form `x' <- e` in every symbolic transition `A_j`.

If Apalache cannot find the expressions with the above properties, it fails.
Consider the example
[`test/tla/Assignments20200309.tla`](../test/tla/Assignments20200309.tla):

```tla
----- MODULE Assignments20200309 -----
VARIABLE a
\* this specification fails, as there it has no expression
\* that can be treated as an assignment
Init == TRUE
Next == a' = a
Inv == FALSE
===============
```

Apalache reports an error as follows:

```console
...
PASS #6: TransitionFinderPass                                     I@09:39:33.527
To understand the error, check the manual:
[https://github.com/konnov/apalache/blob/unstable/docs/manual.md#assignments]
Assignment error: Failed to find assignments and symbolic transitions in InitPrimed E@09:39:33.676
It took me 0 days  0 hours  0 min  1 sec                          I@09:39:33.678
Total time: 1.88 sec                                              I@09:39:33.678
EXITCODE: ERROR (99)
```

This error is cryptic. It does not indicate which parts of the specification
have caused the problem. In the future, we will add better diagnostic in the
assignment finder, see [the open
issue](https://github.com/konnov/apalache/issues/111). Our current approach is
to debug assignments by running TLC first. If running TLC takes too long, you
may try to comment out parts of the specification to find the problematic
action. Although this is tedious, it allows one to find missing assignments
rather quickly.

If you are interested in the technique for finding the assignments and symbolic
transitions that is implemented in Apalache, check our [paper at
ABZ'18](http://forsyte.at/wp-content/uploads/abz2018_full.pdf).  The [journal
version](http://dx.doi.org/https://doi.org/10.1016/j.scico.2019.102361) is
unfortunately behind the Elsevier paywall, which will be lifted after the
two-year embargo period.

<a name="types"></a>

# 8. Type annotations

**NOTE**: [Jure Kukovec](https://forsyte.at/people/kukovec/) is developing
a completely automatic type inference engine. As soon as it is ready, type
annotations will be no longer required. Until that happy day, refer to [type
annotations](types-and-annotations.md).

Apalache requires two kinds of type annotations:
- type annotations for empty sets and sequences, and
- type annotations for records and sets of records.

## 8.1. Empty sets and sequences

Consider the following example
[`test/tla/NeedForTypes.tla`](../test/tla/NeedForTypes.tla):

```tla
------------------------ MODULE NeedForTypes ------------------------------
(**
 * This simple example transforms a set into a sequence.
 *)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS InSet     \* an input set
VARIABLES Left,     \* a storage for the yet untransformed elements
          OutSeq    \* the output sequence

ConstInit == InSet = 1..4

Init ==
    /\ OutSeq = << >>
    /\ Left = InSet

Next ==
    IF Left = {}
    THEN UNCHANGED <<Left, OutSeq>>
    ELSE \E x \in Left:
          /\ OutSeq' = Append(OutSeq, x)
          /\ Left' = Left \ {x}

Inv == InSet = Left \union { OutSeq[i]: i \in DOMAIN OutSeq }
===========================================================================
```

While this example is perfectly fine for TLC, Apalache has to assign types to
the variables, in order to construct SMT constraints. In some cases, Apalache
can infer types completely automatically, e.g., as in the `y2k` example (see
[Section 4](#example)). However, if you run `apalache check
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
objects. Hence, `{}` was assigned the type `FinSet[Unknown]`, that is, a set
of some type. Finally, it found the expression `Left = {}`,
and here the type checker has failed.

To help the type checker, we have to introduce a few type annotations.
But before doing that, we introduce the notation for type annotations
in the specification:

```tla
a <: b == a
```

Apalache treats any application of `<:` as a type annotation. At the same time,
the above definition tells the other tools (e.g., TLC and TLAPS) to ignore
the type annotation.

Now we can help the type checker by rewriting the condition in Next as follows:

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
[`test/tla/NeedForTypesWithTypes.tla`](../test/tla/NeedForTypesWithTypes.tla).

## 8.2. Records and sets of records

Consider the following example in
[`test/tla/Handshake.tla`](../test/tla/Handshake.tla):

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
[`test/tla/HandshakeWithTypes.tla`](../test/tla/HandshakeWithTypes.tla).

Type annotations can be also applied to sets of records. For example:

```tla
[syn |-> BOOLEAN, ack |-> BOOLEAN, seqno |-> Int] <: {MT}
```

You can find more details on the simple type inference algorithm and the type
annotations in [type annotations](types-and-annotations.md).

<a name="recursion"></a>
## 9. Recursive operators and functions

### 9.1. Recursive operators

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

When, we can find an upper bound on the number of iterations, Apalache can
unfold the recursive operator up to this bound. To this end, we define two
additional operators. For instance:

```tla
--------- MC_Rec6 ----------
VARIABLES set, count

INSTANCE Rec6 WITH N <- 3

UNFOLD_TIMES_Sum == 4
UNFOLD_DEFAULT_Sum == 0
============================
```

In this case, Apalache unfolds every call to `Sum` exactly `UNFOLD_TIMES_Sum`
times, that is, four times. On the default branch, Apalache places
`UNFOLD_DEFAULT_SUM`, that is, 0.

### 9.2. Recursive functions

Recursive functions are not supported yet. We do not have an idea of how encode
them.


<a name="theory5"></a>
# 9. Five minutes of theory

**You can safely skip this section**

Given a TLA+ specification, with all parameters fixed, our model checker
performs the following steps:

 1. It automatically extracts symbolic transitions from the specification. This
 allows us to partition the action Next into a disjunction of simpler actions
 `A_1, ..., A_n`.

 2. Apalache translates operators `Init` and `A_1, ..., A_n` to SMT formulas.
 This allows us to explore bounded executions with an SMT solver (we are using
 [Microsoft Z3](https://github.com/Z3Prover/z3)). For instance, a sequence of
 `k` steps, all of which execute action `A_1`, is encoded as a formula `Run(k)`
 that looks like follows:

```tla
[[Init(s_0)]] /\ [[A_1(s_0, s_1)]] /\ ... /\ [[A_1(s_(k-1), s_k)]]
```

To find an execution of length `k` that violates an invariant `Inv`, the tool
adds to the formula `Run(k)` the following constraint:

```tla
[[~Inv(s_0)]] \/ ... \/ [[~Inv(s_k)]]
```

Here, `[[_]]` is the translator from TLA+ to SMT. Importantly, the values for
the states `s_0`, ..., `s_k` are not enumerated as in TLC, but have to be found
by the SMT solver.

If you like to learn more about theory behind Apalache, check the [paper at
OOPSLA19](https://dl.acm.org/doi/10.1145/3360549).

<a name="features"></a>

# 10. Supported language features

Check the [supported features](features.md), [KerA+](kera.md), and
[preprocessing steps](preprocessing.md).
