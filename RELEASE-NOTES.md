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
