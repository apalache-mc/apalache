## 0.44.8 - 2024-03-11

### Bug fixes

- When converting Quint lambdas, derive the return type from the Quint type inferred for  the lambda, rather the type inferred for the body expression, avoiding mismatches with Apalache type variables. (#2856)
