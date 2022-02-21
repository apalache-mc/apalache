## 0.20.4

### Breaking changes

 * The `profiling.csv` file output by the `--smtprof` flag moved into the
   configurable `run-dir`, see #1321
 * The distribution package structure has changed. This shouldn't cause any
   breakage in operation, but may impact some automated deployment pipelines,
   see #1357

### Features

* `UNCHANGED x` now rewrites to `x' := x` instead of `x' = x`, when `x` is a variable name


### Bug fixes

 * Handle `Cardinality(SUBSET S)` without failing, see #1370
