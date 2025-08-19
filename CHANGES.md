<!-- NOTE: This file is generated. Do not write release notes here.
 Notes for unreleased changes go in the .unreleased/ directory. -->
 
## 0.48.0 - 2025-08-19

## 0.47.3 - 2025-08-18

### Breaking changes

- Upgrade Z3 to 4.13.4 (restores linux/arm64 support), see #3057

## 0.47.2 - 2024-12-16

## 0.47.1 - 2024-12-16

### Bug fixes

- Fixed a few problems on parsing Quint and pretty printing TLA, see #3041
- Add extra protection against the SANY race conditions on the filesystem, see #3046
- Fix source tracking in `VCGenerator` to avoid spurious diagnostic messages, see #3010
- Fix a problem when translating Quint nullary operators used polymorphically, see #3044

## 0.47.0 - 2024-10-02

### Breaking changes

- Downgrade z3 to 4.12.6, due to instability of 4.13.0

## 0.46.2 - 2024-10-02

### Bug fixes

- Do not produce `(distinct ...)` for singletons, see #3005
- Show note that expression is unsupported instead of reporting a counterexample claiming that e.g. `{42} \in SUBSET Nat` is false, see #2690

## 0.46.1 - 2024-09-24

### Features

- Periodically print Z3 statistics when `--debug` is on (#2992)
- Parse and pass z3 tuning parameters in the Apalache fine-tuning parameters (#2990)

## 0.45.6 - 2024-09-19

### Features

- Added an `apalache-mc.bat` file to easily start Apalache on Windows, see #2980

## 0.45.4 - 2024-09-02

### Features

- Handle expressions such as  S \in SUBSET T  in ExprOptimizer by rewriting the expression into  \A r \in S: r \in T

### Bug fixes

- Better error reporting for hitting the limits of `SUBSET` expansion, see #2969
- Fix truncation of SMT logs, see #2962

## 0.45.3 - 2024-08-21

### Features

- Added scope-unsafe builder.

## 0.45.2 - 2024-08-19

## 0.45.1 - 2024-08-19

## 0.45.0 - 2024-08-17

### Features

- Handle expressions such as  S \in SUBSET [ a : Int ]  by rewriting the expression into  \A r \in S: DOMAIN r = {"a"} /\ r.a \in Int
- Translate Quint's generate into `Apalache!Gen` (#2916)
- Add `--timeout-smt` to limit SMT queries (#2936)

## 0.44.11 - 2024-05-06

### Features

- TLA+ modules produced by the Shai command `TLA` now include type annotations (#2891)

### Bug fixes

- Fixed a problem where folds produced by the Shai command `TLA` had an invalid form and could not be parsed back (#2891)
- Fixed a problem where bindings from exists and forall operators where not properly sanitized before printing (#2891)
- Fixed a problem where translation from `slice` to `replaceAt` added an incorrect increment to the last argument (#2891)

## 0.44.10 - 2024-03-25

### Bug fixes

- Fix a problem where different quantified variables from Quint received the same TlaType1 var number (#2873).

## 0.44.9 - 2024-03-21

### Bug fixes

- Convert Quint empty tuples as uninterpreted types/values (#2869)

## 0.44.8 - 2024-03-20

### Bug fixes

- Sanitize names while pretty printing to avoid invalid names (#2860)
- When converting Quint lambdas, derive the return type from the Quint type inferred for  the lambda, rather the type inferred for the body expression, avoiding mismatches with Apalache type variables. (#2856)

## 0.44.7 - 2024-03-07

### Features

- Add command to the server's `CmdExecutor` that will reply with formatted TLA+ derived from parsing the provide input. (#2852)

## 0.44.6 - 2024-03-04

### Features

- Increase the Apalache server's  gRPC message size limit from 8MB to 64MB. (#2847)

## 0.44.5 - 2024-02-05

### Bug fixes

- When expected server port is already bound, report clean user error instead of crashing with a traceback  (#2676).

## 0.44.4 - 2024-01-29

### Bug fixes

- When given an empty `.tla` file, report a clean user error instead of crashing with an exception (#2821).

## 0.44.3 - 2024-01-23

### Features

- Parse name of `ASSUME` declarations into IR and preserve them during serialization to JSON, see #2808

### Bug fixes

- fix crash on the arrays encoding when having a subset relation containing infinite sets, see #2810

## 0.44.2 - 2023-12-01

### Bug fixes

- Fix missing support for default match cases in quint conversion (#2792)

## 0.44.1 - 2023-12-01

### Bug fixes

- Fix truncation of SMT debug logs, see #2785

## 0.44.0 - 2023-10-23

### Breaking changes

- Removed the (unused) `--nworkers` flag, see #2275

### Bug fixes

- Continue simulation on SMT timeout in enabledness check, see #2758

## 0.43.0 - 2023-09-18

### Features

- - Revise the ITF format: Use only `{ "#bigint": "num" }`, even for small integers`

## 0.42.0 - 2023-08-21

### Breaking changes

- Update Quint deserialization for compatibility with version > 0.13.0, see #2696

### Bug fixes

- Fix a bug with decoding unconstrained model values of uninterpreted types.

## 0.41.3 - 2023-08-02

### Bug fixes

- Fixed a bug when decoding certain record types, see #2684

## 0.41.2 - 2023-07-24

## 0.41.1 - 2023-07-24

### Bug fixes

- Fixed deserialization of Quint `bigint`s, see #2661

## 0.41.0 - 2023-07-20

### Breaking changes

- Fixed deserialization of large Quint integer values, see #2654

## 0.40.7 - 2023-07-06

### Bug fixes

- Fix a bug when translating certain Quint tuple types, see #2634
- Fix a typing issue when translating Quint name expressions, see #2635

## 0.40.6 - 2023-07-04

### Bug fixes

- Fix an issue with translating Quint type variables, see #2629

## 0.40.5 - 2023-06-30

### Bug fixes

- Increase max inbound gRPC message size, see #2623
- Fix Quint translation of `Nat` and `Int`, see #2621

## 0.40.4 - 2023-06-23

### Bug fixes

- Fixed a bug in pointer propagation, where sets cherrypicked from a powerset would always have the exact same pointers as the base set, instead of some subset thereof (though SMT constraints were added correctly). This broke counterexample reconstruction. See #2606
- Fix translation of nested/shadowed "_" Quint lambda parameters, see #2608

## 0.40.3 - 2023-06-19

### Bug fixes

- Fix handling of applied polymorphic operators in Quint. This increases the number of quint specs that we can successfully verify. (See #2552)

## 0.40.2 - 2023-06-05

### Bug fixes

- Fix deserialization of Quint type and operator definitions. (See #2588)

## 0.40.1 - 2023-06-02

### Features

- Membership tests between records and type-defining sets in `TypeOk` operators are now simplified to `TRUE`. This uses static type information to reduce the costs of verifying specs containing checks of the form  `TypeOk == rec \in [name_1: S1, ..., name_n: Sn]`. (See #723)

### Bug fixes

- Quint `run` declarations are now ignored, allow verification of quint specs including those definitions. (See #2572)

## 0.40.0 - 2023-05-26

### Breaking changes

- Bump Z3 to v4.12.1, see #2565

### Bug fixes

- - fix pretty printing of `x \div y` and `x / y` (#2562)

## 0.30.9 - 2023-05-08

### Bug fixes

- Fix conversion of quint records. See #2542.

## 0.30.8 - 2023-04-17

### Features

- Add support for converting quint record operators. See #2530.

### Bug fixes

- Fix conversion of quint `setBy` operator. See #2531.

## 0.30.7 - 2023-04-11

### Bug fixes

- Fix conversion of quint binding operators to support operator passed by name. See #2520.

## 0.30.6 - 2023-04-01

### Features

- Add conversion of quint operators `range`, `foldr`, `assert`, `select`, and operators over maps (TLA+ functions). See #2439, #2489, #2492, #2493.
- Support conversion of Quin't `nondet` bindings. See #2499.

### Bug fixes

- Fix quint list conversion. See #2495, #2509, #2510.
- Fix conversion of quint let-binding. See #2501.

## 0.30.5 - 2023-03-10

### Breaking changes

- Updated support for quint input, for compatibility with the (forthcoming) Quint v0.8.0. Output from earlier versions of quint will no longer be supported. See #2473 and https://github.com/informalsystems/quint/pull/689.

### Features

- Add support for quint tuples. See #2441.
- Add support for converting (most) quint list operator. See #2440.
- Added support for quint's variadic bindings in `forall` and `exists` operators. See #2471.

## 0.30.4 - 2023-03-08

### Bug fixes

- Fix the typing of quint empty sets during conversion (see #2466)

## 0.30.3 - 2023-03-06

### Features

- Added support for transpiling [quint](https://github.com/informalsystems/quint) booleans, integers, and sets (See #2451, #2449, #2445)

### Bug fixes

- Add support for first-order `CONSTANTS`, see #2389.
- Fixed type checking of specs that use `Print` and `PrintT`, see #2456.

## 0.30.2 - 2023-02-22

### Features

- Added support for inputing a spec written in a small fragment of quint (see #2421).

### Bug fixes

- Fix parsing of lines longer than 999 characters, see #2430

## 0.30.1 - 2022-11-07

### Features

- Server port is now configurable via the `--port` CLI argument or `server.port` configuration key (see #2264).

## 0.30.0 - 2022-10-31

### Breaking changes

- The format of parsing error outputs has been changed. Parsing error messages that used to be prefixed with `Error by TLA+ parser` are now prefixed with `Parsing error` and error messages that used to begin with `Syntax error in annotation:` will now also include the `Parsing error` prefix. This is being recorded as a breaking change since it could break scripts that rely on parsing stdout. (See #2204 and #2242.)

### Features

- Return JSON with success or failure data from RPC calls to the CmdExecutor service (see #2186).

### Bug fixes

- Write the SMT log also to a custom rundir specified with `--run-dir=`, see #2208

## 0.29.2 - 2022-09-26

### Features

- Add [Option.tla](https://github.com/informalsystems/apalache/blob/main/src/tla/Option.tla) module providing support for option types (see #2097).

### Bug fixes

- Fix missing support for single-line comments inside of type annotations (see https://github.com/informalsystems/apalache/issues/2162)

## 0.29.1 - 2022-09-12

### Bug fixes

- Report an error, when --max-error > 1 and no --view is provided, see #2144
- Sort SMT disjuncts generated by `ZipOracle`, see #2149
- Check invariants at step 0 with --discard-disabled=false, see #2158 and #2161

## 0.29.0 - 2022-09-06

### Breaking changes

- Invalid configuration keys found in configuration sources (e.g., `apalache.cfg` files) will now produce a configuration error on load (see #2125).
- The structure of the apalache.cfg has changed. All configuration keys that were previously supported have been moved under the `common` key. You can update your config files by prefixing each key from the previous versions with `commong.key-name`. For an example config file, see https://apalache-mc.org/docs/apalache/config.html#file-format-and-supported-parameters. See #2065.
- Introduce --features=no-rows for the old record syntax and switch to `--features=rows` by default

### Features

- The application configuration is now dumped into the `run-dir` when the `--debug` flag is supplied (see #2134).
- All CLI parameters can now be configured via `apalache.cfg` files. See #2065 and documentation to follow.
- From now on, the type checker reports an error, when the inferred type is more specific than the annotated type, see #2109.
- The options `--init` and `--temporal` can now be given lists of names separated by commas, enabling users to check multiple invariants and temporal properties via the CLI (see #2074).

## 0.28.0 - 2022-08-15

### Breaking changes

- Make example trace output optional on `check` via the `--output-traces` flag, see #2047
- Timestamp in `datailed.log` changed to a full ISO 8601 timestamp, see #2064
- Rename `--save-runs` to `--output-traces`, see #2047

### Features

- Added `funArrays` SMT encoding, see #2011

## 0.27.0 - 2022-08-08

### Breaking changes

- Extended the invariant filter syntax, see #2034

## 0.26.0 - 2022-07-26

### Breaking changes

- Rename base development branch from `unstable` to `main`, this is noted as a breaking change as it could break some CI process or scripts that deploy from source (see #1990)

### Features

- introduce new syntax for type aliases, see #1977

### Documentation

- update the syntax of type aliases in the documentation

## 0.25.10 - 2022-07-18

### Features

- Add RPC to load spec to the experimental Shai server (see #1114)

### Bug fixes

- Add workaround for Sany parsing failures when running parallel instances of Apalache (see #1959)

### Documentation

- Added TLA+ syntax highlighting to the manual, see #1972

## 0.25.9 - 2022-07-11

### Features

- - add generators for variants, see #1900
- Add `VariantTag` and remove `VariantUnwrap`, see #1936

### Bug fixes

- Fixed `IncrementalRenaming` to rename operator parameters, see #1903

### Documentation

- Update HOWTO on types with new records and variants, see #1940
- Update the tutorial on the type checker, see #1942
- Add manual page on new variant types (see #1930)
- Update ADR002 with the new syntax for variants, see #1922

## 0.25.8 - 2022-07-04

### Features

- Add support for temporal properties, enabled via the `--temporal` flag, see #1815
- Support variants in the model checker with `--features=rows`, see #1870
- serialize variants to the ITF format, see #1898
- Annotate counterexample traces to improve readability of temporal properties, see #1823
- Replace PostTypeChecker pass with an additional predicate, see #1878

### Bug fixes

- Add support for checking temporal properties with primed expressions inside, see #1879
- Fixed inlining of nullary polymorphic operators, see #1880
- Fix crash with infinite sets in the arrays encoding, see #1802

## 0.25.7 - 2022-06-13

### Features

- Add support for variants in the typechecker, see #1847

## 0.25.6 - 2022-06-06

### Features

- Always output an example trace, add `--save-runs` flag to save examples for each run of `simulate`, see #1838

### Bug fixes

- Output rare expressions as unserializable to ITF, see #1841
- Fix a problem in comparing functions with empty domains in the arrays encoding, see #1811
- Fix spurious counter-example generation with functions of records in the arrays encoding, see #1840

## 0.25.5 - 2022-05-30

### Features

- Add the experimental command `simulate` that randomly picks transitions, see #1809

## 0.25.4 - 2022-05-30

### Bug fixes

- Fix nested set membership in the arrays encoding, see #1819
- Fixed bug in inlining ASSUME statements, see #1794

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
   https://apalache-mc.org/docs/index.html

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

 * options for fine tuning with `--fine-tuning`, see [tuning](https://github.com/informalsystems/apalache/blob/main/docs/src/apalache/tuning.md)

 * bugfix in logback configuration

## 0.4.0-pre1

 * type annotations and very simple type inference, see the [notes](https://github.com/informalsystems/apalache/blob/main/docs/src/apalache/types-and-annotations.md)

 * a dramatic speed up of many operators by using a `QF_NIA` theory and cherry pick

 * automatic simplification of expressions, including equality

 * decomposition of invariants into smaller pieces


## 0.3.0 [RELEASE]

 * the version presented at the TLA+ community meeting 2018 in Oxford