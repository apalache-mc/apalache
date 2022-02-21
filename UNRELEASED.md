<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
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

### Features
* Add support for functions in the arrays encoding, see #1169
