## 0.45.4 - 2024-09-02

### Features

- Handle expressions such as  S \in SUBSET T  in ExprOptimizer by rewriting the expression into  \A r \in S: r \in T

### Bug fixes

- Better error reporting for hitting the limits of `SUBSET` expansion, see #2969
- Fix truncation of SMT logs, see #2962
