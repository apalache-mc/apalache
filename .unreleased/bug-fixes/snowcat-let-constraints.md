Fixed Snowcat inferring too general types for operators whose parameters are constrained only inside `LET`
definitions, e.g., `(a) => Int` instead of `(Int) => Int` for `F(n) == LET k == n + 1 IN k`. Ill-typed calls of such
operators passed type checking. Also, expressions in `LET` definitions no longer keep polymorphic types after the
enclosing operator fixes them, which crashed the model checker. With `--infer-poly=false`, polymorphic operators are now
reported as type errors (exit code 120) instead of internal errors (exit code 255). See
[model-checker-hardening apalache-typechecker-001](https://github.com/tlaplus/model-checker-hardening/blob/main/findings/apalache-typechecker/apalache-typechecker-001.md).
