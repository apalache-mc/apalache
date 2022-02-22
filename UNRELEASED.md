<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Features

* `UNCHANGED x` now rewrites to `x' := x` instead of `x' = x`, when `x` is a variable name
* Some simple type errors have more informative messages, see #1341

### Bug fixes

* Handle `Cardinality(SUBSET S)` without failing, see #1370
* Add support for functions in the arrays encoding, see #1169
