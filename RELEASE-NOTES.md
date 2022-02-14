## 0.20.3

### Features

 * Implemented `SetAsFun` and use it in counterexamples instead of `:>` and `@@`, see #1319, #1327

### Bug fixes
 * Fixed infinite recursion in `consChain`, see #1307
 * Fixed a bug where some simplified `Or` expressions were not expected by the rewriting rules, see #1285
 * Fixed a bug on broken `--view`, see #1327
