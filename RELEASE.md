## 0.58.3 - 2026-07-09

### Features

- `ConstSimplifier` now simplifies more set expressions: membership in the empty set (`x \in {}` becomes `FALSE`), trivial subset checks (`{} \subseteq S` and `S \subseteq S` become `TRUE`), empty-set identities for an arbitrary set (`{} \cup S`, `S \cup {}`, `{} \cap S`, `S \cap {}`, `{} \ S`, `S \ {}`), and self-operations (`S \cup S`, `S \cap S`, `S \ S`), see #1238.

### Bug fixes

- Fixed type checking of `TLCGet`/`TLCSet`: the register key may be a string (named register, e.g. `TLCGet("level")`) or an integer (numbered register, e.g. `TLCGet(2)`). The key argument is now polymorphic, so an operator mixing both forms type-checks, see #3274.
- Fixed `FoldSet` silently returning the base value when folding over a non-enumerated set such as `SUBSET S` or `[S -> T]`. The set is now marked for expansion, so folds over powersets produce the correct result, and folds over sets whose expansion is unsupported fail loudly instead of returning a wrong answer, see #3385.
- Fix the SANY parsing errors (#3401)
- Fixed a crash (`IllegalArgumentException: Unsupported expression`) in the type checker on unbounded quantifiers `\A x: P` and `\E x: P`. These expressions are now type-checked like their bounded counterparts, and are reported with a proper, source-located error only if they reach the model checker, see #2816.
