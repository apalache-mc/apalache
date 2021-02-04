<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Features

* integration with Java-like annotations in comments, see #504
* support for `Assume(...)` in the type checker
* new command-line option for `typecheck`:
  - enable inference of polymorphic types: `--infer-poly`
* updates to ADR002 and the manual

### Bugfixes

* Boolean values are now supported in TLC config files, see #512
* Proper error on invalid type annotations, the parser is strengthened with Scalacheck, see #332
* Fixed a parsing bug for strings that contain '-', see #539

### Refactoring

* refactoring of the topological sort of declarations, see #122
