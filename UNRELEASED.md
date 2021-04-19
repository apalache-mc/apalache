<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Features

* Checker: Support for CASE without OTHER, see #285

### Bug fixes
* Type checker: Showing an error on missing annotations CONSTANTs or VARIABLEs, see #705
* Model checker: Fix an exception on `Cardinality(a..b) > i`, see #748

### Changed

* IR: simplified `SimpleFormalParam` and `OperFormalParam` into `OperParam`, see #656
* IR: made consistent the names of IR operators (may break JSON compatibility), see #634
