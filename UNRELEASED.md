<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Breaking changes

* `version` command only prints the version, see #1279
* tool and jar location no longer output by default, see #1279

### Features

* Added support for `--output` with `typecheck`, see #1284

### Bug fixes

* Fixed JSON decoder failing on inputs with `"Untyped"`, see #1281
* Fixed JSON decoder failing on inputs with `"FUN_REC_REF"` or `"FUN_REC_CTOR"`
* Correctly resolve higher-order operators in names instances, see #1289
