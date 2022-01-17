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
    - [An Example TLA+ Specification](./apalache/example.md)
    - [Specification Parameters](./apalache/parameters.md)
    - [Symbolic Model Checking with Apalache](./apalache/principles/index.md)
        - [Assignments and symbolic transitions](./apalache/principles/assignments.md)
        - [Folding sets and sequences](./apalache/principles/folds.md)
        - [Invariants: State, Action, Trace](./apalache/principles/invariants.md)
        - [Enumeration of counterexamples](./apalache/principles/enumeration.md)
        - [The Apalache Module](./apalache/principles/apalache-mod.md)
        - [Recursive operators and functions](./apalache/principles/recursive.md)
        - [Naturals](./apalache/principles/naturals.md)
    - [Apalache global configuration file](./apalache/config.md)
    - [TLA+ Execution Statistics](./apalache/statistics.md)
    - [Profiling Your Specification](./apalache/profiling.md)
    - [Five minutes of theory](./apalache/theory.md)
- [TLC Configuration Files](./apalache/tlc-config.md)
- [The Snowcat Type Checker](./apalache/typechecker-snowcat.md)
- [Supported Features](./apalache/features.md)
- [Known Issues](./apalache/known-issues.md)
- [Antipatterns](./apalache/antipatterns.md)
- [TLA+ Preprocessing](./apalache/preprocessing.md)
- [Fine Tuning](./apalache/tuning.md)
- [Assignments and Symbolic Transitions in Depth](./apalache/assignments-in-depth.md)
- [KerA: kernel logic of actions](./apalache/kera.md)


# HOWTOs

- [Overview](HOWTOs/index.md)
- [How to write type annotations](./HOWTOs/howto-write-type-annotations.md)
- [How to use uninterpreted types](./HOWTOs/uninterpretedTypes.md)

# Tutorials

- [Overview](./tutorials/index.md)
- [The Snowcat:snowflake::cat: Type Checker](./tutorials/snowcat-tutorial.md)
- [Symbolic Model Checking](./tutorials/symbmc.md)

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
- [Apalache operators](./lang/apalache-operators.md)
- [Modules, Extends, and Instances]()

# Idiomatic TLA+

- [Introduction](./idiomatic/index.md)
- [Keep state variables to the minimum](idiomatic/000keep-minimum-state-variables.md)
- [Update state variables with assignments](idiomatic/001assignments.md)
- [Apply primes only to state variables](idiomatic/002primes.md)
- [Avoid sets of mixed records](./idiomatic/003record-sets.md)


# Design Documents

- [ADR-002: types and type annotations](./adr/002adr-types.md)
- [ADR-003: transition executor (TRex)](./adr/003adr-trex.md)
- [ADR-004: code annotations](./adr/004adr-annotations.md)
- [ADR-005: JSON Serialization Format](./adr/005adr-json.md)
- [RFC-006: unit tests and property-based tests](./adr/006rfc-unit-testing.md)
- [ADR-007: restructuring](./adr/007adr-restructuring.md)
- [ADR-008: exceptions](./adr/008adr-exceptions.md)
- [ADR-009: outputs](./adr/009adr-outputs.md)
- [ADR-011: alternative SMT encoding using arrays](./adr/011adr-smt-arrays.md)
- [ADR-015: ITF: informal trace format](./adr/015adr-trace.md)
