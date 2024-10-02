## 0.46.2 - 2024-10-02

### Bug fixes

- Do not produce `(distinct ...)` for singletons, see #3005
- Show note that expression is unsupported instead of reporting a counterexample claiming that e.g. `{42} \in SUBSET Nat` is false, see #2690
