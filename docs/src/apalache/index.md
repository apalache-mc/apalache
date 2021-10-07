# Apalache Manual

**Authors: Igor Konnov, Jure Kukovec, Andrey Kuprianov, Shon Feder**

**Contact: {igor,jure,andrey,shon} at informal.systems**

Apalache is a symbolic model checker for
[TLA+](https://lamport.azurewebsites.net/tla/tla.html). (*Still looking for a
better tool name.*) Our model checker is a recent alternative to
[TLC](https://lamport.azurewebsites.net/tla/tools.html?unhideBut=hide-tlc&unhideDiv=tlc).
Whereas TLC enumerates the states produced by the behaviors of a TLA+
specification, Apalache translates the verification problem to a set of logical
constraints. These constraints are solved by an [SMT
solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories), for
instance, by [Microsoft's Z3](https://github.com/Z3Prover/z3). That is, Apalache
operates on formulas (i.e., _symbolicly_), not by enumerating states one by one
(i.e., _state enumeration_).

Apalache is working under the following assumptions:

 1. As in TLC, all specification parameters are fixed and finite, i.e., the
    system state is initialized with integers, finite sets, and functions of
    finite domains and co-domains.
 2. As in TLC, all data structures evaluated during an execution are finite,
    e.g., a system specification cannot operate on the set of all integers.
 3. Only finite executions of bounded length are analyzed.
