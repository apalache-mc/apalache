## 0.62.3 - 2026-10-01

### Features

- Rewrite `t \in S \X T` into `t[1] \in S /\ t[2] \in T` instead of constructing the cartesian product,  see #1931.

### Bug fixes

- Fix stack overflow on large sets in the expression builder, see https://github.com/tlaplus/model-checker-hardening/issues/65
- Fix PrettyWriter to always parenthesize set-map bodies: { (e) : x \in S }. See [model-checker-hardening apalache-printer-010](https://github.com/tlaplus/model-checker-hardening/blob/main/findings/apalache-printer/apalache-printer-010.md).
- Fixed a crash when a fold's operator tests membership in a singleton set literal, see #3479.
- Fixed PrettyWriter changing expression scope when hoisting lambda argument declarations into LET-IN expressions, see [model-checker-hardening#88](https://github.com/tlaplus/model-checker-hardening/issues/88).
- Fix rewriting of function sets with empty domains or co-domains. See #3478.
