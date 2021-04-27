<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Features

 * apalache quits with a non-zero exit code on counterexample or error, see #249

### Bug fixes

* Parser: supporting annotations in multiline comments, see #718
* Parser: supporting TLA+ identifiers in annotations, see #768
* Parser: better parser for annotations, see #757
* The command `config --enable-stats=true` creates `$HOME/.tlaplus` if needed, see #762

### Changes

 * Builds: removed scoverage from maven, to improve build times
