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
