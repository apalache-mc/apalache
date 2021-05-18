# Summary

[Overview](./index.md)

# Tutorials

- [Type Checker Tutorial](./tutorials/snowcat-tutorial.md)

# Apalache User Manual

- [Introduction](./apalache/index.md)
- [Getting Started](./apalache/getting-started.md)
    - [Shall I use Apalache or TLC?](./apalache/apalache-or-tlc.md)
    - [System Requirements](./apalache/system-reqs.md)
    - [Installation](./apalache/installation/index.md)
        - [Prebuilt Packages](./apalache/installation/jvm.md)
        - [Docker](./apalache/installation/docker.md)
        - [Source](./apalache/installation/source.md)
    - [Running the Tool](./apalache/running.md)
    - [Invariants: State, Action, Trace](./apalache/invariants.md)
    - [Enumeration of counterexamples](./apalache/enumeration.md)
    - [TLA+ Execution Statistics](./apalache/statistics.md)
    - [An Example TLA+ Specification](./apalache/example.md)
    - [Specification Parameters](./apalache/parameters.md)
    - [Principles of Symbolic Model Checking with Apalache](./apalache/principles.md)
    - [The Apalache Module](./apalache/apalache-mod.md)
    - [Profiling Your Specification](./apalache/profiling.md)
    - [Five minutes of theory](./apalache/theory.md)
- [TLC Configuration Files](./apalache/tlc-config.md)
- [The Snowcat Type Checker](./apalache/typechecker-snowcat.md)
- [Supported Features](./apalache/features.md)
- [Known Issues](./apalache/known-issues.md)
- [TLA+ Preprocessing](./apalache/preprocessing.md)
- [Fine Tuning](./apalache/tuning.md)
- [KerA: kernel logic of actions](./apalache/kera.md)
- [Assignments in Apalache](./apalache/assignments.md)

# HOWTOs

- [Overview](HOWTOs/index.md)
- [How to write type annotations](./HOWTOs/howto-write-type-annotations.md)

# Tutorials

- [Overview](./tutorials/index.md)
- [The Snowcat:snowflake::cat: Type Checker](./tutorials/snowcat-tutorial.md)

# TLA+ Language Manual for Engineers

- [Introduction](./lang/index.md)
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
    - [Top-level operator definitions](./lang/user/top-level-operators.md)
    - [LET-IN definitions](./lang/user/let-in.md)
    - [Higher-order operators definitions](./lang/user/higher-order-operators.md)
    - [Anonymous operator definitions](./lang/user/lambdas.md)
    - [Recursive operator definitions](./lang/user/recursive-operators.md)
    - [Local operator definitions](./lang/user/local-operators.md)
    - [Recursive functions](./lang/user/recursive-functions.md)
- [Modules, Extends, and Instances]()

# Idiomatic TLA+

- [Introduction](./idiomatic/index.md)
- [Keep state variables to the minimum](idiomatic/000keep-minimum-state-variables.md)
- [Update state variables with assignments](idiomatic/001assignments.md)
- [Apply primes only to state variables](idiomatic/002primes.md)

# Design Documents

- [ADR-002: types and type annotations](./adr/002adr-types.md)
- [ADR-004: code annotations](./adr/004adr-annotations.md)
- [RFC-006: unit tests and property-based tests](./adr/006rfc-unit-testing.md)
