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
