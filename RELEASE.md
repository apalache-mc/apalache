## 0.40.1 - 2023-06-02

### Features

- Membership tests between records and type-defining sets in `TypeOk` operators are now simplified to `TRUE`. This uses static type information to reduce the costs of verifying specs containing checks of the form  `TypeOk == rec \in [name_1: S1, ..., name_n: Sn]`. (See #723)

### Bug fixes

- Quint `run` declarations are now ignored, allow verification of quint specs including those definitions. (See #2572)
