<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Breaking changes

 * Rework module lookup (drops support for `TLA_PATH`), see #1491

### Features

 * Look up modules in the same directory, see #1491
 * Support for the community module `SequencesExt`, see #1539
 * Support for the community module `BagsExt`, see #1555

### Improvements

 * Pack arithmetic expressions and comparisons into a single SMT constraint,
   see #1540 and #1545

### Bug fixes

 * Fix uncaught `FileNotFoundException` in commands called on nonexistent files,
   see #1503
 * Fix equality on sequences, see #1548, #1554
