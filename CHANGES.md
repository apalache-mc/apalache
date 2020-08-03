## Unreleased #unstable
 * introduced the tool module `Typing.tla`, see #162
 * introduced the tool module `Apalache.tla`, see #183
 * Lookup for modules using TLA_PATH, see #187
 * Simplify JSON format to make it suitable for JsonPath queries, see #153

## 0.7.0 [RELEASE]

 * Importer from JSON, see #121
 * optimization for `Cardinality(S) >= k`, see #118
 * sound translation of `LOCAL` operators, see #49
 * unrolling recursive operators, see #67
 * support for recursive functions that return integers and Booleans, see #84
 * new IR for recursive functions, see #84 and TlaFunctionOper.recFunDef
 * parser for the TLC configuration files, see #76
 * exporter to JSON, see #77
 * counterexamples in the TLC and JSON, see #45 and #116
 * fixed exit codes `EXITCODE: OK` and `EXITCODE: ERROR (<code>)`
 * normal error messages and failure messages with stack traces
 * bugfixes: #12, #104, #148

## 0.6.1 [SNAPSHOT]

 * Critical bugfix in the optimization of set comprehensions like `\E x \in {e: y \in S}: f`

 * Bugfix for #108: the model checker was skipping the `FALSE` invariant,
   due to an optimization

## 0.6.0 [RELEASE]

 * Using `z3` version `4.8.7`

 * A 2-8x speedup for 5 out 16
   [benchmarks](https://github.com/informalsystems/apalache-tests),
   due to the optimizations and maybe switching to z3 4.8.x.
 
 * Distributing the releases with docker as `apalache/mc`

 * The results of intermediate passes are printed in TLA+ files
   in the `x/*` directory: `out-analysis.tla`, `out-config.tla`,
   `out-inline.tla`, `out-opt.tla`, `out-parser.tla`,
   `out-prepro.tla`, `out-priming.tla`, `out-transition.tla`,
   `out-vcgen.tla`

 * The model checker is translating only `KerA+` expressions,
   which are produced by `Keramelizer`

 * Multiple optimizations that were previously done by rewriting
   rules were move to the preprocessing phase, produced by
   `ExprOptimizer`

 * Introducing Skolem constants for `\E x \in S: P`, such
   expressions are decorated with `Skolem`

 * Introducing `Expand` for `SUBSET S` and `[S -> T]`, when
   they must be expanded

 * Translating `e \in a..b` to `a <= e /\ e <= b`, whenever possible

 * Supporting sequence concatenation: `<<1, 2>> \o <<4, 5>>`

 * Short-circuiting and lazy-circuiting of `a /\ b` and `a \/ b`
   are disabled by default (see docs/tuning.md on how to enable them)

 * Introduced `PrettyWriter` to nicely print TLA+ expressions
   with proper indentation

 * The preprocessing steps -- which were scattered across the code
   -- are extracted in the module `tla-pp`,
   which contains: `ConstAndDefRewriter`, `ConstSimplifier`,
   `Desugarer`, `Normalizer`, see [preprocessing](docs/preprocessing.md)

 * Bounded variables are uniquely renamed by `Renaming`
   and `IncrementalRenaming`

 * Massive refactoring of the TLA intermediate representation

 * TLA+ importer stopped chocking on the rare TLA+ syntax, e.g.,
   `ASSUME` and `THEOREM`

 * Backtracking expressions to their source location in a TLA+ spec

 * `LET-IN` is translated into `LetInEx` in `tlair`

 * Nullary LET-IN expressions (without arguments) are processed by
   the model checker directly, no expansion needed

 * The assignment solver has been refactored. The assignments are
   now translated to `BMC!<-`, for instance, `x' <- S`

 * Constant assignments in `ConstInit` are now preprocessed correctly

 * User operators are not translated to `TlaUserOper` anymore,
   but are called with `TlaOper.apply`

 * Importing `tla2tools.jar` from Maven Central

## 0.5.2

 * A backport of the build system from 0.6.0

## 0.5.1

 * The artifact accepted at OOPSLA19

## 0.5.0 [RELEASE]

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

 * options for fine tuning with `--fine-tuning`, see [tuning](https://github.com/informalsystems/apalache/blob/unstable/docs/tuning.md)

 * bugfix in logback configuration

## 0.4.0-pre1

 * type annotations and very simple type inference, see the [notes](https://github.com/informalsystems/apalache/blob/unstable/docs/types-and-annotations.md)

 * a dramatic speed up of many operators by using a `QF_NIA` theory and cherry pick

 * automatic simplification of expressions, including equality

 * decomposition of invariants into smaller pieces


## 0.3.0 [RELEASE]

 * the version presented at the TLA+ community meeting 2018 in Oxford
