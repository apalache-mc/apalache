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

### Bug fixes

 * Fix uncaught `FileNotFoundException` in commands called on nonexistent files,
   see #1503
 * Fix equality on sequences, see #1548, #1554
