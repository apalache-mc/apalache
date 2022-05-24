<!-- NOTE: This file is generated. Do not write release notes here.
 Notes for unreleased changes go in the .unreleased/ directory. -->
 
## 0.25.3 - 2022-05-20

### Breaking changes

- Introduce dedicated exit codes for type-checking errors, parser errors, and evaluation errors (e.g., due to unsupported language constructs or operators), see #1749

### Features

- Support sound records (over rows) in the model checker, see #1717

### Bug fixes

- Fix potential non-determinism when picking from `[S -> T]`, see #1753
- Fix the bug in uninterpreted types, see #1792

## 0.25.2

### Features

 * Support sound records (over rows) in the model checker, see #1717

## 0.25.1
     
### Features

 * Support for native ARM64/AArch64 JVMs (and thus Apple Silicon), see #751

### Bug fixes

 * Fix usage of sets of function sets in the arrays encoding, see #1680
 * Fix an uncaught exception when setting up the output manager, see #1706
 * Handle heap memory exhaustion gracefully, see #1711

## 0.25.0

### Breaking changes

 * Recommended JDK version was bumped to JDK17, see #1662
 * Add the option `--features` to enable experimental features, see #1648
 * Never report a deadlock when `--no-deadlock=1`, see #1679

### Features

* Include the version number in `detailed.log`, see #1678
* Add the option `--features` to enable experimental features, see #1648
* Never load TLC config files by default, see #1676
* Experimental type unification over rows, new records, and variants, see #1646
* Experimental type checking for records over rows, see #1688

### Bug fixes

* Fix references to `--tune-here` (actually `--tuning-options`), see #1579
* Not failing when assignment and `UNCHANGED` appear in invariants, see #1664

## 0.24.1

### Breaking changes

 * Rename `--tuning` to `--tuning-options-file`, see #1579

### Bug fixes

 * Fix references to `--tune-here` (actually `--tuning-options`), see #1579

## 0.24.0

### Breaking changes
* `RECURSIVE` operators and functions are no longer supported, see #1569
* rename Apalache `FoldSet` and `FoldSeq` to `ApaFoldSet` and `ApaFoldSeqLeft`, see #1617

### Features

* Add the operator `Apalache!Guess`, see #1590 and #888
* Extend the type parser to support ADR014 (experimental), see #1602
* Keramelizer now rewrites \subseteq using forall quantification, see #1408
* Builtin operators can be passed as arguments to HO operators, see #1630
* Optimize set membership for record sets, see #1629
## 0.23.1

### Bug fixes

* Fix the generation of SMT instances with the `--debug` flag, see #1594
* Fix symbolic link generation in 'make' on Windows, see #1596

## 0.23.0

### Breaking changes

 * Rework module lookup (drops support for `TLA_PATH`), see #1491

### Features

 * Look up modules in the same directory, see #1491
 * Support for the community module `SequencesExt`, see  #1539
 * Support for the community module `BagsExt`, see #1555
 * Support for the community module `Folds`, see #1558

### Improvements

 * Pack arithmetic expressions and comparisons into a single SMT constraint,
   see #1540 and #1545

### Bug fixes

 * Fix uncaught `FileNotFoundException` in commands called on nonexistent files,
   see #1503
 * Fix equality on sequences, see #1548, #1554

## 0.22.3

### Features

 * An optimization in function application, see #1500

### Bug fixes

 * Fix stack overflow and out-of-memory in function operators, see #1498
 * Fix function application static check in arrays encoding, see #1490
 * Add support for the community modules FiniteSetsExt and Functions, see #1484
 * Add support for Bags, see #1527

## 0.22.2

### Features
 * Enable records in the arrays encoding, see #1288
 * Enable the remaining TLA+ features in the arrays encoding, see #1418
 * Implement the sequence constructor `Apalache!MkSeq`, see #1439
 * Add support for `Apalache!FunAsSeq`, see #1442
 * Implement `EXCEPT` on sequences, see #1444
 * Cache default values, see #1465

### Bug fixes
 * Fixed bug where TLA+ `LAMBDA`s wouldn't inline outside `Fold` and `MkSeq`, see #1446
 * Fix the comment preprocessor to extract annotations after a linefeed, see #1456
 * Fix the failing property-based test, see #1454
 * Fixed a bug where call-by-name embedding wasn't properly called recursively 

## 0.22.1

### Bug fixes

 * Fix a corner case in `\E x \in S: P`, see #1426

## 0.22.0

### Breaking changes

* Complete rework of sequences, see #1353
## 0.21.1

### Breaking changes

 * The `profiling.csv` file output by the `--smtprof` flag moved into the
   configurable `run-dir`, see #1321
 * The distribution package structure has changed. This shouldn't cause any
   breakage in operation, but may impact some automated deployment pipelines,
   see #1357

### Features

* `UNCHANGED x` now rewrites to `x' := x` instead of `x' = x`, when `x` is a variable name
* Some simple type errors have more informative messages, see #1341

### Bug fixes

* Handle `Cardinality(SUBSET S)` without failing, see #1370
* Add support for functions in the arrays encoding, see #1169

## 0.20.3

### Features

 * Implemented `SetAsFun` and use it in counterexamples instead of `:>` and `@@`, see #1319, #1327

### Bug fixes
 * Fixed infinite recursion in `consChain`, see #1307
 * Fixed a bug where some simplified `Or` expressions were not expected by the rewriting rules, see #1285
 * Fixed a bug on broken `--view`, see #1327

## 0.20.2

### Bug fixes

 * Fix polymorphic types when the type checker is called twice, see #1300

## 0.20.1

### Breaking changes

* `version` command only prints the version, see #1279
* tool and jar location no longer output by default, see #1279

### Features

* Added support for `--output` with `typecheck`, see #1284

### Bug fixes

* Fixed JSON decoder failing on inputs with `"Untyped"`, see #1281
* Fixed JSON decoder failing on inputs with `"FUN_REC_REF"` or `"FUN_REC_CTOR"`
* Correctly resolve higher-order operators in names instances, see #1289
* Fix ITF output for singleton functions, see #1293

## 0.20.0

### Breaking changes

- Switched build system from maven to sbt (note, will only cause breakage in
  pipelines that build from source), See #1234.

### Features

 * Completely remove TlcOper and replace it with a custom TLA+ module, see #1253

### Bug fixes

 * Fix the semantics of @@ by using the TLC definition, see #1182, #951, #1234
 * Fix unexpected polymorphism, see #1262
  

## 0.19.3

### Bug fixes

 * Fix the ITF writer on empty functions, see #1232

## 0.19.2

### Design

 * ADR-014 on precise type checking for records and variants, see #1151

### Features

 * Output in the Informal Trace Format, see #1220

### Bug fixes

 * Add constant simplification rules that may improve performance in specific scenarios, see #1206
 * Fix expansion of `~` in configured paths, see #1208
 * Fix a bug where an implication with its left side simplified to the `TRUE` constant was incorrectly translated, see #1206

## 0.19.1

### Features

* New errors for the following constant simplification scenarios (see #1191):
  1. Division by 0
  1. Mod (%) by 0
  1. Negative expoents
  1. Expoents bigger than an Integer
  1. Expoential operations that would overflow `BigInt`

## 0.19.0

### Breaking changes

* The global config file is now named `$HOME/.tlaplus/apalache.cfg`, see #1160

### Features

* Support for a local config file (defaulting to `$PWD/.apalache.cfg`) see #1160

### Bug fixes

* Fix the use of set union in the array encoding, see #1162
* Fix preprocesor's normalization of negated temporal formulas and negated `LET .. IN` expressions, see #1165

## 0.18.1

### Bug fixes

* Fix the use of set minus in the array encoding, see #1152

## 0.18.0

### Features

 * Add bug report templates, see #1094

 * Improve the format of uninterpreted constants to name_OF_TYPE, see #1130

### Bug fixes

 * Remove duplicate function indices when decoding symbolic states, fixes #962

 * Translate `a^b` for non-constant `a` and `b`, fixes #1136

### Refactoring

* Change the format of type exceptions, see #1090

 * Remove duplicate function indices when decoding symbolic states, fixes #962

 * Improve error messaging for Seq, see #1126 and #1127

### Documentation

 * Restructure and update the Apalache manual:
   https://apalache.informal.systems/docs/index.html

## 0.17.5

### Bug fixes

 * Fix computation of principal types, see #1084
 * Fix error leaving contents in run-dir as empty files, see #1119

### Features

 * Added support for sets to the SMT encoding with arrays, see #1092

## 0.17.4

### Features

* Add `--run-dir` flag, enabling users to write outputs directly to a known and
  stable location, see #1081

## 0.17.3

### Features

   * Added sort-distinction for model values, see #570

### Bug fixes

   * Fixed handling of polymorphic operators in folds, see #1085

## 0.17.2

### Bug fixes

* Fix regression breaking `--output` file format detection in parser command, see
  #1079

## 0.17.1

### Bug fixes

* Fix regression breaking behavior of `--output` flag, see #1072, #1073

## 0.17.0

### Features

 * Add smt-encoding option to CLI check command, see #1053
 * Added CLI and configuration interface for managing generated outputs, see #1025, #1036, #1062, #1065

## 0.16.5

### Bug fixes

 * Propagate constraints passed in --cinit, see #1023
 * Propagate constraints passed ASSUME, see #880

## 0.16.4


## 0.16.3


### Bug fixes

* Fix type checker to complain about polymorphism in the post phase, see #931

### Features

* Enumerated files containing intermediate module states, see #993

### Delivery

* Move docker containers to the GitHub container registry, see #1013

## 0.16.2

### Features

 * improve SMT encoding by removing unused let-definitions, see #995

### Bug fixes

 * Fixed a bug caused by big numbers on annotations, see #990

## 0.16.1

### Bug fixes

 * Fixed a heisenbug caused by EXCEPT on records, which used unsorted keys, see #987
 * Fixed unsound skolemization that applied to let-definitions, see #985

## 0.16.0

### Features

* Support for let-polymorphism in `typecheck`, see #869
* Support for let-polymorphism in `check`, see #953

## 0.15.13

### Bug fixes

 * Fix the profiler, see #963
 * Handle exceptions in record update edge case, see #917

## 0.15.12

### Bug fixes

* Fix infinite recursion in the type unifier, see #925
* Fix unhandled errors on non-existent record field access, see #874
* Fix unhandled `MatchError` on invalid operator type annotations, see #919

## 0.15.11

### Features

   * Implemented support for SelectSeq, see #873

### Bug fixes

   * Fixed crash on specs with no variables, see #871

## 0.15.10

### Bug fixes

 * Fixed a bug which made Fold(Set/Seq) unusable in Init or CInit

## 0.15.9

### Features

* Parser: parse error on TLAPS syntax such as `Inv!2`, see #876
* Checker: support for Fold(Set/Seq), see #693

### Bug fixes

* Fixed #540
* Fixed #593

## 0.15.8

### Bug fixes

* Tool: no empty log on help message, see #830

### Documentation

* revision 2 of RFC006 on unit testing

## 0.15.7

### Features

* Checker: enumerating multiple counterexamples, see #542 and #827

### Documentation

* Manual: manual page on enumerating counterexamples and view abstraction, see #542

* links to ADR005

## 0.15.6

### Features

* Checker: support for action invariants, see #801
* Checker: support for trace invariants, see #819

### Improvements

* Add type information to overriding error, see #823

## 0.15.5

### Changes

* Docker: Use openjdk-16 for the runtime in the app image, see #807
* Documentation: Introduce TypeAlises operator convention, see #808
* tlair: TlaExLevelFinder and TlaDeclLevelFinder to compute TLA+ levels, see #811

### Bug fixes

* Printer: replacing '$' and '!' with supported characters, see #574
* Printer: normalizing module names and writing TLA+ & JSON in all passes, see #785

## 0.15.4

### Documentation

* RFC006 on unit testing: see #741

### Features

* apalache quits with a non-zero exit code on counterexample or error, see #249
* type checker: supporting one-line comments in types, see #773

### Bug fixes

* Parser: supporting annotations in multiline comments, see #718
* Parser: supporting TLA+ identifiers in annotations, see #768
* Parser: better parser for annotations, see #757
* Parser: fixed two bugs in the declaration sorter, see #645 and #758
* Printer: fixed the output for EXCEPT, see #746
* Printer: fixed pretty printing of annotations, see #633
* Printer: extending the standard modules, see #137
* The command `config --enable-stats=true` creates `$HOME/.tlaplus` if needed, see #762
* IO: replaced calls to deprecated JsonReader/JsonWriter. out-parser.json is now compliant with the new format, see #778

### Changes

* Builds: removed scoverage from maven, to improve build times
* Docs: updated ADR002 and HOWTO on type annotations to explain comments
* CLI: Users can set JVM args via the JVM_ARGS env var, see #790

## 0.15.3

### Features

* Checker: Support for CASE without OTHER, see #285

### Bug fixes
* Type checker: Showing an error on missing annotations CONSTANTs or VARIABLEs, see #705
* Model checker: Fix an exception on `Cardinality(a..b) > i`, see #748

### Changed

* IR: simplified `SimpleFormalParam` and `OperFormalParam` into `OperParam`, see #656
* IR: made consistent the names of IR operators (may break JSON compatibility), see #634

## 0.15.2

### Features

* Manual: added manual page on known issues
* IR: added `Apalache!Gen` to generate bounded data structures, see #622
* Checker: added support for `Apalache!Gen`, see #622
* Tool: added a new command `test` to quickly evaluate an action in isolation, see #622

## 0.15.1

### Features

* Manual: added a tutorial on the type checker Snowcat, see #689
* Language manual: add types for the standard operators, see #547
* Type checker: add support for type aliases,
  e.g., `@typeAlias FOO = [a: Int, b: Int]`, see #704
* Manual: updated the HOWTO on type annotations with type aliases

## 0.15.0

### Features

* Model checker: receiving the types from with the type checker Snowcat, see #668 and #350
* Model checker and type checker: Snowcat is the only way to compute types now
* Type checker: the old Apalache type annotations are no longer supported, see #668
* Type checker: tagging all expressions with the reconstructed types, see #608
* Type checker: handling TLA+ labels like `lab("a", "b") :: e`, see #653
* Type checker: always treating `<<...>>` in `UNCHANGED <<...>>` as a tuple, see #660
* Type checker: handling the general case of EXCEPT, see #617
* Preprocessing: handling the general case of EXCEPT, see #647

### Changed

* Preprocessing: massive refactoring of the passes to support types. This may have introduced unexpected bugs.
* Model checker: translation rules for records and functions have been modified, in order to support new types. Bugs to
  be expected.
* Intermediate representation: renamed BmcOper to ApalacheOper. Its operators have the prefix `Apalache!` now.

### Removed

* Unused rewriting rules and `FailPredT` in the model checker, see #665
* Intermediate representation: removed non-standard operators subsetProper, supset, supseteq, see #615
* Intermediate representation: removed TlaArithOper.{sum,prod}, as they are not standard, see #580
* Intermediate representation: removed TlaOper.chooseIdiom

## 0.11.0

### Features
 * Type checker: supporting TLC operators, see #601

### Bug fixes

 * Parser: propagating type annotations in INSTANCES, see #592 and #596

### Removed

 * Type checker: removed `Typing.tla`, `AssumeType`, and `##`, see #518

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

 * options for fine tuning with `--fine-tuning`, see [tuning](https://github.com/informalsystems/apalache/blob/unstable/docs/src/apalache/tuning.md)

 * bugfix in logback configuration

## 0.4.0-pre1

 * type annotations and very simple type inference, see the [notes](https://github.com/informalsystems/apalache/blob/unstable/docs/src/apalache/types-and-annotations.md)

 * a dramatic speed up of many operators by using a `QF_NIA` theory and cherry pick

 * automatic simplification of expressions, including equality

 * decomposition of invariants into smaller pieces


## 0.3.0 [RELEASE]

 * the version presented at the TLA+ community meeting 2018 in Oxford