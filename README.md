# APALACHE project

A symbolic model checker for TLA+

__master__: [![Build Status](https://travis-ci.org/konnov/apalache.svg?branch=master)](https://travis-ci.org/konnov/apalache)
&nbsp;&nbsp;&nbsp;
__unstable__: [![Build Status](https://travis-ci.org/konnov/apalache.svg?branch=unstable)](https://travis-ci.org/konnov/apalache)

Apalache translates TLA+ in the logic supported by the SMT solvers, for instance, [Microsoft Z3](https://github.com/Z3Prover/z3). Apalache can check inductive invariants (for fixed or bounded parameters) and check safety of bounded executions (bounded model checking). To see the list of supported
TLA+ constructs, check the [supported features](docs/features.md). In general,
Apalache runs under the same assumptions as TLC.

## Releases

Check the [releases page](https://github.com/konnov/apalache/releases).
You can always try the latest cool features in the [unstable branch](https://github.com/konnov/apalache/tree/unstable).

## Getting started

Read the [user manual](docs/manual.md).

## Academic papers

To read an academic paper about the theory behind APALACHE,
check our [paper at OOPSLA19](https://forsyte.at/wp-content/uploads/kkt-oopsla19.pdf). Related reports and publications can be found at the
[Apalache page at TU Wien](http://forsyte.at/research/apalache/).
