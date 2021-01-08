# Summary

# Apalache User Manual

- [Introduction](./README.md)
- [Getting Started](./manual.md)
    1. [Shall I use Apalache or TLC?](./manual.md#apalacheOrTlc)
    1. [System requirements](./manual.md#sysreq)
    1. [Installation](./manual.md#installation)
    1. [An example of a TLA+ specification](./manual.md#example)
    1. [Setting up specification parameters](./manual.md#parameters)
    1. [Running the tool](./manual.md#running)
    1. [Principles of symbolic model checking with Apalache](./manual.md#principles)
       1. [Assignments and symbolic transitions](./manual.md#assignments)
       1. [Type annotations](./manual.md#types)
       1. [Recursive operators and functions](./manual.md#recursion)
    1. [The Apalache module](./manual.md#apalacheMod)
    1. [Profiling your specification](./manual.md#profiling)
    1. [Five minutes of theory](./manual.md#theory5)
- [TLC Configuration Files](./tlc-config.md)
- [Types and Annotations](./types-and-annotations.md)
- [Supported Features](./features.md)
- [TLA+ Preprocessing](./preprocessing.md)
- [Fine Tuning](./tuning.md)
- [KerA: kernel logic of actions](./kera.md)

# TLA+ Language Manual for Engineers

- [Introduction](./lang/README.md)
- [The standard operators of TLA+](./lang/standard-operators.md)
    - [Booleans](./lang/booleans.md)
    - [Control And Nondeterminism](./lang/control-and-nondeterminism.md)
    - [Conditionals](./lang/conditionals.md)
    - [Integers](./lang/integers.md)
    - [Sets](./lang/sets.md)
    - [Logic](./lang/logic.md)
    - [Functions](./lang/functions.md)
    - [Records](./lang/records.md)
    - [Tuples](./lang/tuples.md)
    - [Sequences](./lang/sequences.md)
    - [Bags]()
- [User-defined operators](./lang/user-operators.md)
- [Modules, Extends, and Instances]()

# Idiomatic TLA+

- [Introduction](./idiomatic/README.md)
- [Keep state variables to the minimum](idiomatic/000keep-minimum-state-variables.md)
- [Update state variables with assignments](idiomatic/001assignments.md)
- [Apply primes only to state variables](idiomatic/002primes.md)

# Design Documents

- [ADR-002: types and type annotations](./adr/002adr-types.md)
