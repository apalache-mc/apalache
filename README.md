# APALACHE project

A symbolic model checker for TLA+

__master__: [![Build Status](https://travis-ci.org/konnov/apalache.svg?branch=master)](https://travis-ci.org/konnov/apalache)
&nbsp;&nbsp;&nbsp;
__unstable__: [![Build Status](https://travis-ci.org/konnov/apalache.svg?branch=unstable)](https://travis-ci.org/konnov/apalache)

To read an academic paper about the theory behind APALACHE,
check our [paper at OOPSLA19](https://forsyte.at/wp-content/uploads/kkt-oopsla19.pdf).

The current version of the tool is neither parameterized, nor it is using
abstractions. As a first step, we are working on a symbolic bounded model
checker that runs under the same assumptions as TLC. To see the list of supported
TLA+ constructs, check the [supported features page](docs/features.md).
Our tool runs simple type inference, in order to encode TLA+ expressions in
 [Microsoft Z3](https://github.com/Z3Prover/z3). Check the note on
[type inference and annotations](docs/types-and-annotations.md) to get an idea of
the supported TLA+ expressions and hints provided by the user.

Related reports and publications can be found at the
[apalache page](http://forsyte.at/research/apalache/).

## Releases

Check the [releases page](https://github.com/konnov/apalache/releases).
So far, we have not been releasing often. You can always try the latest cool
features in the [unstable branch](https://github.com/konnov/apalache/tree/unstable).

## Getting Started

Read the [manual](doc/manual.md).
