<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Bug fixes

* Add support for stable output in `latest` directory of the configured
  `out-dir`, see #1081
* Add support for `--output` flag to `check` command, which specifies where
  counterexamples are to be written, see #1081
* Fix regression breaking `--output` file format detection in parser command, see
  #1079
