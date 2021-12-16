<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Breaking changes

* The global config file is now named `$HOME/.tlaplus/apalache.cfg`, see #1160

### Features

* Support for a local config file (defaulting to `$PWD/.apalache.cfg`) see #1160

### Bug fixes

* Fix the use of set union in the array encoding, see #1162
* Fix preprocesor's normalization of negated temporal formulas and negated `LET .. IN` expressions, see #1165
