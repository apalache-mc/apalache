<!-- NOTE:
     This file is generated. Do not write release notes here.
     Notes for unreleased changes go in ./UNRELEASED.md -->

## 0.10.1

### Features

* Support for `FunAsSeq` conversion in the type checker, see #223
* The parser outputs annotations, see #502

### Documentation

* HOWTO on writing type annotations, see #571

### Bug fixes

* Fixed name collisions on LOCAL operators and LOCAL INSTANCE, see #576
* Parser: a higher-order operator calling a higher-order operator, see #575
* Type checker: support for recursive functions of multiple arguments, see #582
* Type checker: support for tuple unpacking in recursive functions, see #583

## 0.10.0

### Features

* integration with Java-like annotations in comments, see #504
* support for `Assume(...)` in the type checker
* new command-line option for `typecheck`:
  - enable inference of polymorphic types: `--infer-poly`
* updates to ADR002 and the manual
* support for parallel assignments `<<x', y'>> = <<1, 2>>`, see #531
* always sorting declarations with topological sort (changes the order of the operator definitions), see #122

### Bugfixes

* Boolean values are now supported in TLC config files, see #512
* Promoting Desugarer to run as the first preprocessing pass, see #531
* Proper error on invalid type annotations, the parser is strengthened with Scalacheck, see #332
* Fixed a parsing bug for strings that contain '-', see #539
* Typechecking quantifiers over tuples, see #482

## 0.9.0

### Features

* new sequential model checker that is using TransitionExecutor, see #467
* new command-line options, see #467 and the manual for details:
  * choose the algorithm: `--algo=(offline|incremental)`
  * pre-check, whether a transition disabled, discard the disabled transitions: `--discard-disabled`
  * do not check for deadlocks: `--no-deadlock`
  * pass tuning parameters in CLI: `--tune-here`
* parsing in-comment Java-like annotations, see #226
* tracking the source of variable/constant declarations and operator
  definitions in the TLA+ Parser, see #262

### Bug fixes

* the new sequential model checker has uncovered a bug that was not found
  by the old model checker, see #467

### Documentation

* ADR004: In-comment annotations for declarations (of constants, variables, operators)

## 0.8.3

## Bug fixes

 * Fixed path of jar in ZIP distribution, reported in #500, see #506

## 0.8.2

### Bug fixes

 * handling big integers, see #450
 * better parsing of SPECIFICATION in TLC configs, see #468
 * expanding tuples in quantifiers, see #476
 * unfolding UNCHANGED for arbitrary expressions, see #471
 * unfolding UNCHANGED <<>>, see #475

### Features

 * constant simplification over strings, see #197
 * propagation of primes inside expressions,
   e.g., (f[i])' becomes f'[i'] if both f and i are state variables

## 0.8.1

### Bug fixes

 * critical bugfix in unique renaming, see #429
 * include missing {Apalache,Typing}.tla modules in release package, see #447

### Features

 * opt-in for statistics collection (shared with TLC and TLA+ Toolbox), see #288

### Architecture

 * new layer of TransitionExecutor (TRex), see `at.forsyte.apalache.tla.bmcmt.trex.*`

### Documentation

 * Compile the manuals into [a static
  site](http://informalsystems.github.io/apalache/docs/) using
  [mdBook](https://github.com/rust-lang/mdBook), see #400
 * Description of top-level user operators, see #419
 * ADR003: [Architecture of TransitionExecutor](./docs/internal/adr/003adr-trex.md)

## 0.8.0 [RELEASE]

 * use openjdk-9 for deterministic Apalache Docker images, see #318
 * support for advanced syntax in TLC configs, see #208
 * random seed for z3, see docs/tuning.md and #318
 * correct translation of chained substitutions in INSTANCEs, see #143
 * friendly messages for unexpected expressions, see #303
 * better operator inlining, see #283
 * support for standard modules that are instantiated with LOCAL INSTANCE, see #295
 * support for LAMBDAs, see #285 and #289
 * bugfix in treatment of recursive operators, see #273
 * no theories in the model checker due to types, see #22
 * operators and checker caches made Serializable
 * better diagnostics for the recursive operators, see #272
 * verbose output for the config parser, see #266
 * Use a staged docker build, reducing container size ~70%, see #195
 * Use [Z3-TurnKey](https://github.com/tudo-aqua/z3-turnkey) instead of a
   bespoke Z3 build, see #219
 * Use Z3 version 4.8.7.1, see #219
 * Re-stabilized tests on recursive operators, see #344
 * Changed the assignment paradigm; solver now finds assignments without SMT, see #366

## 0.7.2 [RELEASE]

 * fixed an omitted version number update

## 0.7.1 [RELEASE]

 * safe checks for the user options in ConfigurationPassImpl, see #193
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
