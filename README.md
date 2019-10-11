# APALACHE project

A symbolic model checker for TLA+

__master__: [![Build Status](https://travis-ci.org/konnov/apalache.svg?branch=master)](https://travis-ci.org/konnov/apalache)
&nbsp;&nbsp;&nbsp;
__unstable__: [![Build Status](https://travis-ci.org/konnov/apalache.svg?branch=unstable)](https://travis-ci.org/konnov/apalache)

To get an intuition about how APALACHE is working,
check our [paper at OOPSLA19](https://forsyte.at/wp-content/uploads/kkt-oopsla19.pdf).

The current version of the tool is neither parameterized, nor it is using
abstractions. As a first step, we are working on a symbolic bounded model
checker that runs under the same assumptions as TLC. To see the list of supported TLA+ constructs, check the [supported features page](docs/features.md).
Our tool runs simple type inference, in order to encode TLA+ expressions in
 [Microsoft Z3](https://github.com/Z3Prover/z3). Check the note on
[type inference and annotations](docs/types-and-annotations.md) to get an idea of
the supported TLA+ expressions and hints provided by the user. 

Related reports and publications can be found at the
[apalache page](http://forsyte.at/research/apalache/).

## Releases

Check the [releases page](https://github.com/konnov/apalache/releases).
As the tool is in the early development stage, there are a few releases. 

To try the latest features, you can download
[the latest unstable build](https://github.com/konnov/apalache/releases/tag/latest-unstable).

## Preparing the spec

Similar to TLC, before running the tool, you have to specify the input parameters.
Since we do not have integration with the TLA+ Toolbox yet,
we require all constants to be initialized in a spec. There are two ways to do that.

#### Option 1: Replace constants with operators
For instance, assume your spec contains a constant ``N`` for the number of processes
and a constant ``Values`` for the set of possible values:

```TLA
CONSTANT N, Values
``` 

Replace them with the operators that define concrete values:

```TLA
\* CONSTANT N, Values
N == 4
Values == {0, 1}
```

#### Option 2: Initialize constants with ConstInit

This approach is similar to the ``Init`` operator, but applied to the constants.
We define a special operator, e.g., called ``ConstInit``: 

```TLA
CONSTANT N, Values

ConstInit ==
  /\ N \in {4}
  /\ Values \in {{0, 1}}
```

Note that in the current version, an assignments to a constants ``c`` should be
written as ``c \in S``, where ``S`` is a set (you can use ``SUBSET S`` and ``[S -> T`` as well]).
Moreover, ``ConstInit`` should be a conjunction of such assignments and possibly
of additional constraints on the constants.

As a bonus of this approach, you can have _parameterized though bounded_ constraints on the constants.
For example:

```TLA
CONSTANT N, Values

ConstInit ==
  /\ N \in 3..10
  /\ Values \in SUBSET 0..4
  /\ Values /= {}
```

The model checker will try the instances for all the combinations of
the parameters specified in ``ConstInit``, that is, in our example, it will
consider ``N \in 3..10`` and all non-empty value sets that are subsets of ``0..4``.

#### Type annotations

Additionally, whenever you are using an empty set ``{}``, an empty sequence ``<<>>``,
or a set of records with different sets of fields, you have to annotate these
expressions with types, see [type inference and annotations](docs/types-and-annotations.md).

## Running the binaries

First, make sure that you have installed [Oracle JRE 8](https://www.oracle.com/technetwork/java/javase/downloads/jre8-downloads-2133155.html)
(or JDK8) and [Microsoft Z3 4.7.1](https://github.com/Z3Prover/z3/releases/tag/z3-4.7.1).

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

The tool will display only the important messages. A detailed log can be found in `detailed.log`.

## Building from sources

To build the tool, you will need the following standard packages: Java 8 SDK,
Scala, and Maven. You will also need [Z3 Prover
4.7.1](https://github.com/Z3Prover/z3) and [TLA tools](http://lamport.azurewebsites.net/tla/tools.html).
Both Z3 and TLA+ tools can
be automatically installed in your local Maven repository by running the script
`./3rdparty/install-local.sh`. __WARNING: Z3 API has been changed in version
4.8.0, so make sure that you install version 4.7.1.__

To build the complete package, including the dependencies, type:

```bash
$ mvn package
```

