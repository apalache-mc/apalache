## 0.58.0 - 2026-05-29

### Features

- Added experimental CVC5 support as an SMT solver backend for the OOPSLA19 encoding.

### Bug fixes

- Fixed a `ClassCastException` / `AssertionError` crash during `--temporal` checking when `Next` contains an `IF` or `CASE` whose branches return sets or functions and whose body contains a nested `\/` or `/\` of three or more terms, see #2107.
