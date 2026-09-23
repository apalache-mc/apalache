Fix Snowcat inferring too general types for operators whose parameters are constrained only inside `LET`
definitions, e.g., `(a) => Int` instead of `(Int) => Int` for `F(n) == LET k == n + 1 IN k`.
