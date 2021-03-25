<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->

### Features

* Model checker: receiving the types from with the type checker Snowcat, see #668 and #350
* Model checker and type checker: Snowcat is the only way to compute types now
* Type checker: the old Apalache type annotations are no longer supported, see #668
* Type checker: tagging all expressions with the reconstructed types, see #608
* Type checker: handling TLA+ labels like `lab("a", "b") :: e`, see #653
* Type checker: always treating `<<...>>` in `UNCHANGED <<...>>` as a tuple, see #660
* Preprocessing: handling the general case of EXCEPT, see #647

### Changed

* Preprocessing: massive refactoring of the passes to support types. This may have introduced unexpected bugs.
* Model checker: translation rules for records and functions have been modified, in order to support new types. Bugs to
  be expected.
* Intermediate representation: renamed BmcOper to ApalacheOper. Its operators have the prefix `Apalache!` now.

### Removed

* Intermediate representation: removed TlaOper.chooseIdiom

### Changed

* Intermediate representation: removed TlaArithOper.{sum,prod}, as they are not standard, see #580

### Removed

* Intermediate representation: removed non-standard operators subsetProper, supset, supseteq, see #615

### Known issues

* Multiple-update expressions `[f EXCEPT ![i1][i2] = e1, ![i1][i3] = e2]` may produce incorrect results, see #647
