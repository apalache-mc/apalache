<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->

### Features

* Type checker: tagging all expressions with the reconstructed types, see #608
* Type checker: experimental option `check --with-snowcat`, see #632
* Type checker: handling TLA+ labels like `lab("a", "b") :: e`, see #653
* Preprocessing: handling the general case of EXCEPT, see #647

### Changed

* Preprocessing: massive refactoring of the passes to support types. This may have introduced unexpected bugs.

### Known issues

* Multiple-update expressions `[f EXCEPT ![i1][i2] = e1, ![i1][i3] = e2]` may produce incorrect results, see #647
