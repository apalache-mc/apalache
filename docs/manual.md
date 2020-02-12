# APALACHE manual

**Version 0.6.0**

**Author: Igor Konnov, igor at informal.systems**

# Introduction

APALACHE is a symbolic model checker for [TLA+](https://lamport.azurewebsites.net/tla/tla.html) (*still looking for a better tool name*). Our model checker is a recent alternative to [TLC](https://lamport.azurewebsites.net/tla/tools.html?unhideBut=hide-tlc&unhideDiv=tlc).
Whereas TLC enumerates states that are produced by behaviors of a TLA+ specification, APALACHE translates the verification problem to a set of logical constraints. These constraints are solved by an [SMT solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories), for instance, by [Microsoft Z3](https://github.com/Z3Prover/z3). That is, APALACHE is operating in terms of formulas (i.e., _symbolic_), not enumerating states one by one (i.e., _state enumeration_).

APALACHE is working under the following assumptions:

 1. As in TLC, all specification parameters are fixed and finite, e.g., the system is initialized integers, finite sets, and functions of finite domains and co-domains.

 2. As in TLC, all data structures evaluated during an execution are finite, e.g., a system specification cannot operate on the set of all integers.

 3. Only finite executions of bounded length are analyzed.


# Table of Contents

 1. [Shall I use APALACHE or TLC?](#apalacheOrTlc)
 1. [System requirements](#sysreq)
 1. [Installation](#installation)
 1. [A simple TLA+ specification](#example)
 1. [Setting up specification parameters](#parameters)
 1. [Running the tool](#running)
 1. [Type annotations](#types)
 1. [Five minutes of theory](#theory5)
 1. [Supported language features](#features)


# 1. Shall I use Apalache or TLC? <a name="apalacheOrTlc"></a>

We recommend to start with TLC. It is mature, well-documented, and well-integrated into TLA+ Toolbox. Once you have debugged your TLA+ specification, and TLC is still producing too many reachable states, switch to Apalache. We are using this approach at [Informal Systems](https://informal.systems/).

# 2. System requirements

Every commit to [master](https://github.com/konnov/apalache) and [unstable](https://github.com/konnov/apalache/tree/unstable) is built with [Travis CI](https://travis-ci.org/konnov/apalache) on MacOS (xcode9.3 and JDK 1.8.0) and Linux (OpenJDK8). If you like to run APALACHE in Windows, use a docker image. Check the [Docker manual](https://docs.docker.com/docker-for-windows/) and the section on [Using a docker image](#useDocker).

As APALACHE is using Microsoft Z3 as a backend SMT solver, the required memory largely depends on Z3. We recommend to allocate at least 4GB of memory for the tool.

# 3. Installation <a name="installation"></a>

There are two ways to run APALACHE: (1) Download and run a docker image, or (2) Build APALACHE from sources and run the compiled package. If you just like to try the tool, we recommend to use the docker image. If you like to run the tool on daily basis or to contribute to the project, we recommend to build from the sources. In the following, we write `$APALACHE_HOME` to refer
to the directory, where Apalache is cloned.

## 3.1. Using a docker image <a name="useDocker"></a>   

**Starting with release 0.6.0, we will publish Docker images for every release**.

To build a docker image of APALACHE, issue the following command at `$APALACHE_HOME`:

```
docker image build -t apalache:0.6.0 .
```

To run an APALACHE image, issue the command:

```
docker container run --rm --name apa apalache:0.6.0 <args>
```

## 3.2.  Building from sources

1. Install `git`.
1. Clone the git repository: `git clone https://github.com/konnov/apalache.git`
1. Install [Oracle JDK8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html) or OpenJDK8. **You have to install version 8, as Scala will not compile!. See [compatibility table](https://docs.scala-lang.org/overviews/jdk-compatibility/overview.html).**

   For instance, that is how one installs JDK8 at Debian Linux 9. Since Debian dropped OpenJDK8, we have to do a few hoops to install Oracle JDK8:
  - Run `sudo apt-get install java-package`
  - Download JDK of `Java SE 8u*` from the [Oracle page](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html) as a tgz archive
  - Run `make-jpkg <downloaded-archive>.tgz`
  - Run `sudo dkpg -i <file-by-make-jpkg>.deb`
  - Make sure that `java -version` indeed shows Java 1.8.x
1. Install [Apache Maven](https://maven.apache.org/). For instance, using Debian Linux:
  - Run `sudo apt-get install maven`
1. Run `make`. This command will install Microsoft Z3, compile APALACHE
   and assemble the package

# 4. A simple TLA+ specification <a name="example"></a>

To illustrate the features of APALACHE, we are using the following TLA+ specification, which can be found in `$APALACHE_HOME/test/tla/y2k.tla`:

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

# 5. Setting up specification parameters <a name="parameters"></a>

Similar to TLC, APALACHE requires the specification parameters to be restricted to finite values. In contrast to TLC, there is a way to initialize parameters by writing a symbolic constraint, see [Section 5.3](#ConstInit).

## 5.1. Using INSTANCE

You can set the specification parameters, using the standard `INSTANCE` expression of TLA+. For instance, below is the example `$APALACHE_HOME/test/tla/y2k_instance.tla`, which instantiates `y2k.tla`:

```tla
---------------------------- MODULE y2k_instance ----------------------------
VARIABLE year, hasLicense

INSTANCE y2k WITH BIRTH_YEAR <- 80, LICENSE_AGE <- 18
=============================================================================
```

The downside of this approach is that you have to declare the variables of the extended specification.

## 5.2. Convention over configuration

```tla
---------------------------- MODULE y2k_override ----------------------------
EXTENDS y2k

OVERRIDE_BIRTH_YEAR == 80
OVERRIDE_LICENSE_AGE == 18
=============================================================================
```

## 5.3. ConstInit predicate <a name="ConstInit"></a>

This approach is similar to the ``Init`` operator, but applied to the constants. We define a special operator, e.g., called ``ConstInit``. For instance, below is the example `$APALACHE_HOME/test/tla/y2k_cinit.tla`:

```tla
---------------------------- MODULE y2k_cinit ----------------------------
EXTENDS y2k

ConstInit ==
    /\ BIRTH_YEAR \in 0..99
    /\ LICENSE_AGE \in 10..99
=============================================================================
```

To use `ConstInit`, pass it as the argument to `apalache-mc`. For instance, for `y2k_cinit`, we would run the model checker as follows:

```tla
$ cd $APALACHE_HOME/test/tla
$ ../../bin/apalache-mc check --inv=Safety \
  --length=20 --cinit=ConstInit y2k_cinit.tla
```

**Parameterized initialization**. As a bonus of this approach, APALACHE allows one to check
a specification over a bounded set of parameters.
For example:

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
$ bin/apalache-mc check [--init=Init] [--cinit=ConstInit] [--next=Next] [--inv=Inv] [--length=10] [--tuning=filename] myspec.tla
```

The arguments are as follows:

  * ``--init`` specifies the initialization predicate, the default name is ``Init``
  * ``--next`` specifies the transition predicate, the default name is ``Next``
  * ``--cinit`` specifies the constant initialization predicate, optional
  * ``--inv`` specifies the invariant to check, optional
  * ``--length`` specifies the upper bound on the length of the finite executions to explore
  * ``--tuning`` specifies the properties file that stores the options for [fine tuning](docs/tuning.md)

If you like to check an inductive invariant ``Inv``, you can run two commands:   

```bash
$ bin/apalache-mc check --init=Inv --inv=Inv --length=1 myspec.tla
```

and

```bash
$ bin/apalache-mc check --init=Init --inv=Inv --length=0 myspec.tla
```

Make sure that ``Inv`` contains necessary constraints on the shape of the variables.
Usually, ``TypeOK`` as the first line of the invariant is exactly what is needed.

## 6.2. Examples

to-be-added

## 6.3. Detailed output

**Detailed information.** The tool will display only the important messages. A detailed log can be found in `detailed.log`.

Additionally, the model checker passes produce intermediate TLA+ files are in the run-specific directory `x/hh.mm-DD.MM.YYYY-<id>`:

  - File `out-parser.tla` is produced as a result of parsing and importing into Apalache TLA IR.
  - File `out-config.tla` is produced as a result of substituting CONSTANTS, as described in [Section 5](#parameters).
  - File `out-inline.tla` is produced as a result of inlining operator definitions and LET-IN definitions.
  - File `out-priming.tla` is produced as a result of replacing constants and variables in `ConstInit` and `Init` with their primed versions.
  - File `out-vcgen.tla` is produced as a result of extracting verification conditions, e.g., invariants to check.
  - File `out-prepro.tla` is produced as a result of running all preprocessing steps.
  - File `out-transition.tla` is produced as a result of finding assignments and symbolic transitions.
  - File `out-opt.tla` is produced as a result of expression optimizations.
  - File `out-analysis.tla` is produced as a result of analysis, e.g.,
    marking Skolemizable expressions and expressions to be expanded.

# 7. Type annotations <a name="types"></a>

**NOTE**: [Jure Kukovec](https://forsyte.at/people/kukovec/) is developing
a completely automatic type inference engine. As soon as it is ready, type annotations be no longer required.

We will add examples. For the moment, check [type annotations](./docs/types-and-annotations).

# 8. Five minutes of theory <a name="theory5"></a>

**You can safely skip this section**

Given a TLA+ specification, with all parameters fixed, our model checker performs the following steps:

 1. It automatically extracts symbolic transitions from the specification. This allows us to partition the action Next into a conjunction of simpler actions `A_1, ..., A_n`.

 2. APALACHE translates the operators `Init` and `A_1, ..., A_n` to SMT formulas. This allows us to explore bounded executions with an SMT solver (we are using [Microsoft Z3](https://github.com/Z3Prover/z3)). For instance, a sequence of `k` steps, all of which execute action `A_1`, is encoded as a formula `Run(k)` that looks like follows:

```tla
[[Init(s_0)]] /\ [[A_1(s_0, s_1)]] /\ ... /\ [[A_1(s_(k-1), s_k)]]
```

To find an execution of length `k` that violates an invariant `Inv`, the tool adds to the formula `Run(k)` the following constraint:

```tla
[[~Inv(s_0)]] \/ ... \/ [[~Inv(s_0)]]
```

Here, `[[_]]` is the translator from TLA+ to SMT. Importantly, the values for the states `s_0`, ..., `s_k` are not enumerated as in TLC, but have to be found by the SMT solver.

If you like to learn more about theory behind APALACHE,
check the [following paper](https://forsyte.at/wp-content/uploads/kkt-oopsla19.pdf).


# 9. Supported language features <a name="features"></a>

Check the [supported features](features.md), [KerA+](kera.md), and [preprocessing steps](preprocessing.md).
