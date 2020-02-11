## 0.5.2

 * A backport of the build system from 0.6.0

## 0.5.1

 * The artifact accepted at OOPSLA19

## 0.5.0

 * support for top-level `INSTANCE` and `INSTANCE WITH` operators

 * command-line option `--cinit` to initialize `CONSTANTS` with a predicate

 * support for `[SUBSET S -> T]` and `[S -> SUBSET T]`

 * support for `\E x \in Nat: p` and `\E x \in Int: p`

 * limited support for `Int` and `Nat`

 * support for sequence operators: `<<..>>`, `Head`, `Tail`, `Len`, `SubSeq`, `DOMAIN`
 * support for FiniteSets: `Cardinality` and `FiniteSet`

 * support for TLC operators: `@@ and :>`

 * support for complex `EXCEPT` expressions

 * support for nested tuples in `UNCHANGED`, e.g., `UNCHANGED << <<a>>, <<b, c>> >>`

 * speed up by using constants instead of uninterpreted functions

 * options for fine tuning with `--fine-tuning`, see [tuning](https://github.com/konnov/apalache/blob/unstable/docs/tuning.md)

 * bugfix in logback configuration

## 0.4.0-pre1

 * type annotations and very simple type inference, see the [notes](https://github.com/konnov/apalache/blob/unstable/docs/types-and-annotations.md)
 
 * a dramatic speed up of many operators by using a `QF_NIA` theory and cherry pick
 
 * automatic simplification of expressions, including equality
 
 * decomposition of invariants into smaller pieces
 
 
## 0.3.0

 * the version presented at the TLA+ community meeting 2018 in Oxford

