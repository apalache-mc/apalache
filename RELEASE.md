## 0.25.8 - 2022-07-04

### Features

- Add support for temporal properties, enabled via the `--temporal` flag, see #1815
- - Support variants in the model checker with `--features=rows`, see #1870
- - serialize variants to the ITF format, see #1898
- Annotate counterexample traces to improve readability of temporal properties, see #1823
- - Replace PostTypeChecker pass with an additional predicate, see #1878

### Bug fixes

- Add support for checking temporal properties with primed expressions inside, see #1879
- Fixed inlining of nullary polymorphic operators, see #1880
- Fix crash with infinite sets in the arrays encoding, see #1802
