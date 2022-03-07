<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Features

 * Implement the sequence constructor `Apalache!MkSeq`, see #143
 * Add support for `Apalache!FunAsSeq`, see #1442
 * Implement `EXCEPT` on sequences, see #1444

### Bug fixes
 * Fixed bug where TLA+ `LAMBDA`s wouldn't inline outside `Fold` and `MkSeq`, see #1446