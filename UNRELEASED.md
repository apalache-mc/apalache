<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
     
### Features

 * Support for native ARM64/AArch64 JVMs (and thus Apple Silicon), see #751

### Bug fixes

 * Fix usage of sets of function sets in the arrays encoding, see #1680
 * Fix an uncaught exception when setting up the output manager, see #1706
 * Handle heap memory exhaustion gracefully, see #1711
