<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Breaking changes

 * Introduce dedicated exit codes for type-checking errors, parser errors, and
   evaluation errors (e.g., due to unsupported language constructs or
   operators), see #1749

### Features

 * Support sound records (over rows) in the model checker, see #1717

### Bug fixes
 
 * Fix potential non-determinism when picking from `[S -> T]`, see #1753
 * Fix the bug in uninterpreted types, see #1792
