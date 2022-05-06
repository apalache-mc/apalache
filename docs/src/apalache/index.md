# Getting Started

Apalache is a symbolic model checker for the [specification language][]
[TLA+][]. As such, it is a recent alternative to the explicit-state model
checker [TLC][].

## Apalache vs. TLC

Whereas TLC enumerates the states produced by the behaviors of a TLA+
specification, Apalache translates the verification problem to a set of logical
constraints. These constraints are solved by an [SMT solver][SMT], for example,
by [Microsoft Z3][]. That is, Apalache operates on formulas (i.e.,
_symbolically_), not by enumerating states one by one (i.e., _state
enumeration_).

### Shall I use Apalache or TLC?

Depending on the specification you wrote, either TLC or Apalache may be more
efficient in checking it. While TLC is a mature tool, Apalache is still
experimental, so be prepared to use the command-line and to help us discover
bugs.

## Assumptions

Apalache is working under the following assumptions:

 1. As in TLC, all specification parameters are fixed and finite, i.e., the
    system state is initialized with integers, finite sets, and functions of
    finite domains and co-domains.
 2. As in TLC, all data structures evaluated during an execution are finite,
    e.g., a system specification cannot operate on the set of all integers.
 3. Only finite executions of bounded length are analyzed.

[specification language]: https://en.wikipedia.org/wiki/Specification_language
[TLA+]: https://lamport.azurewebsites.net/tla/tla.html
[TLC]: https://lamport.azurewebsites.net/tla/tools.html?unhideBut=hide-tlc&unhideDiv=tlc
[SMT]: https://en.wikipedia.org/wiki/Satisfiability_modulo_theories
[Microsoft Z3]: https://github.com/Z3Prover/z3
[Informal Systems]: https://informal.systems/

## Conventions

Throughout this manual, we use the following conventions:

- `APALACHE_HOME` is used as shorthand for the path to a local copy of the
  Apalache source code.
