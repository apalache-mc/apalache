<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Documentation

* RFC006 on unit testing: see #741

### Features

* apalache quits with a non-zero exit code on counterexample or error, see #249
* type checker: supporting one-line comments in types, see #773

### Bug fixes

* Parser: supporting annotations in multiline comments, see #718
* Parser: supporting TLA+ identifiers in annotations, see #768
* Parser: better parser for annotations, see #757
* Parser: fixed two bugs in the declaration sorter, see #645 and #758
* Printer: fixed the output for EXCEPT, see #746
* Printer: fixed pretty printing of annotations, see #633
* Printer: extending the standard modules, see #137
* The command `config --enable-stats=true` creates `$HOME/.tlaplus` if needed, see #762
* IO: replaced calls to deprecated JsonReader/JsonWriter. out-parser.json is now compliant with the new format, see #778

### Changes

* Builds: removed scoverage from maven, to improve build times
* Docs: updated ADR002 and HOWTO on type annotations to explain comments
* CLI: Users can set JVM args via the JVM_ARGS env var, see #790
