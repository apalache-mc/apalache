# Syntax of TLC Configuration Files

**Author:** Igor Konnov, 2020

This file presents the syntax of
[TLC](http://lamport.azurewebsites.net/tla/tools.html) configuration files
in [EBNF](https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form) and
comments on the treatment of its sections in
[Apalache](https://github.com/informalsystems/apalache). A detailed discussion
on using the config files with TLC can be found in Leslie Lamport's 
[Specifying Systems],
Chapter 14 and in
[Current Versions of the TLA+ Tools](https://lamport.azurewebsites.net/tla/current-tools.pdf).
In particular, the TLA+ specification of TLC configuration files
is given in Section 14.7.1. The standard parser can be found in
[`tlc2.tool.impl.ModelConfig`](https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tlc2/tool/impl/ModelConfig.java).
As the configuration files have simple syntax, we implement our own parser in
Apalache.

```ebnf
// The configuration file is a non-empty sequence of configuration options.
config ::=
    options+

// Possible options, in no particular order, all of them are optional.
// Apalache expects Init after Next, or Next after Init.
options ::=
    Init
  | Next
  | Specification
  | Constants
  | Invariants
  | Properties
  | StateConstraints
  | ActionConstraints
  | Symmetry
  | View
  | Alias
  | Postcondition
  | CheckDeadlock

// Set the initialization predicate (over unprimed variables), e.g., Init.
Init ::=
    "INIT" ident

// Set the next predicate (over unprimed and primed variables), e.g., Next.
Next ::=
    "NEXT" ident

// Set the specification predicate, e.g., Spec.
// A specification predicate usually looks like Init /\ [][Next]_vars /\ ...
Specification ::=
    "SPECIFICATION" ident

// Set the constants to specific values or substitute them with other names.
Constants ::=
    ("CONSTANT" | "CONSTANTS") (replacement | assignment)*

// Replace the constant in the left-hand side
// with the identifier in the right-hand side.
replacement ::=
    ident "<-" ident

// Replace the constant in the left-hand side
// with the constant expression in the right-hand side.
assignment ::=
    ident "=" constExpr

// A constant expression that may appear in
// the right-hand side of an assignment.
constExpr ::=
    modelValue
  | integer
  | string
  | "{" "}"
  | "{" constExpr ("," constExpr)* "}"

// The name of a model value, see Section 14.5.3 of Specifying Systems.
// A model value is essentially an uninterpreted constant.
// All model values are distinct from one another. Moreover, they are
// not equal to other values such as integers, strings, sets, etc.
// Apalache treats model values as strings, which it declares as
// uninterpreted constants in SMT.
modelValue ::= ident

// An integer (no bit-width assumed)
integer ::=
      <string matching regex [0-9]+>
    | "-" <string matching regex [0-9]+>

// A string, starts and ends with quotes,
// a restricted set of characters is allowed (pre-UTF8 era, Paxon scripts?)
string ::=
    '"' <string matching regex [a-zA-Z0-9_~!@#\$%^&*-+=|(){}[\],:;`'<>.?/ ]*> '"'

// Set an invariant (over unprimed variables) to be checked against
// every reachable state.
Invariants ::=
    ("INVARIANT" | "INVARIANTS") ident*

// Set a temporal property to be checked against the initial states.
// Temporal properties reason about finite or infinite computations,
// which are called behaviors in TLA+. Importantly, the computations
// originate from the initial states.
// APALACHE IGNORES THIS CONFIGURATION OPTION.
Properties ::=
    ("PROPERTY" | "PROPERTIES") ident*

// Set a state predicate (over unprimed variables)
// that restricts the state space to be explored.
// APALACHE IGNORES THIS CONFIGURATION OPTION.
StateConstraints ::=
    ("CONSTRAINT" | "CONSTRAINTS") ident*

// Set an action predicate (over unprimed and primed variables)
// that restricts the transitions to be explored.
// APALACHE IGNORES THIS CONFIGURATION OPTION.
ActionConstraints ::=
    ("ACTION-CONSTRAINT" | "ACTION-CONSTRAINTS") ident*

// Set the name of an operator that produces a set of permutations
// for symmetry reduction.
// See Section 14.3.3 in Specifying Systems.
// APALACHE IGNORES THIS CONFIGURATION OPTION.
Symmetry ::=
    "SYMMETRY" ident

// Set the name of an operator that produces a state view
// (some form of abstraction).
// See Section 14.3.3 in Specifying Systems.
// APALACHE IGNORES THIS CONFIGURATION OPTION.
View ::=
    "VIEW" ident

// Whether the tools should check for deadlocks.
// APALACHE IGNORES THIS CONFIGURATION OPTION.
CheckDeadlock ::=
    "CHECK_DEADLOCK" ("FALSE" | "TRUE")

// Recent feature: https://lamport.azurewebsites.net/tla/current-tools.pdf
// APALACHE IGNORES THIS CONFIGURATION OPTION.
Postcondition ::=
    "POSTCONDITION" ident

// Very recent feature: https://github.com/tlaplus/tlaplus/issues/485
// APALACHE IGNORES THIS CONFIGURATION OPTION.
Alias ::=
    "ALIAS" ident

// A TLA+ identifier, must be different from the above keywords.
ident ::=
    <string matching regex [a-zA-Z_]([a-zA-Z0-9_])*>

```

[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html

