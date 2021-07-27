<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Bug fixes

* Fix infinite recursion in the type unifier, see #925
* Fix unhandled errors on non-existent record field access, see #874
* Fix unhandled `MatchError` on invalid operator type annotations, see #919
