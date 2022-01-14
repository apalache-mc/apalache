<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Features

* Add constant simplification rules that may improve performance in specific scenarios, see #1206

### Bug Fixes

* Fix expansion of `~` in configured paths, see #1208
* Fix a bug where an implication with its left side simplified to the `TRUE` constant was incorrectly translated, see #1206
