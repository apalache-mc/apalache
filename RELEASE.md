## 0.62.2 - 2026-08-26

### Bug fixes

- Align operator priorities with SANY so that `PrettyWriter` parenthesizes sequential composition and set-prefix operators correctly.
- Fixed JSON IR deserialization of labeled expressions, see #3466
- Render non-stuttering actions and action or fairness subscripts with valid TLA+ delimiters in `PrettyWriter` output.
- Render unbounded `CHOOSE`, `\A`, and `\E` binders as valid TLA+ in `PrettyWriter` output.
- Parenthesize labelled expressions when embedded in larger `PrettyWriter` output so that they preserve their grouping in TLA+.
- Fixed exponential backtracking when parsing nested type annotations, which could exhaust the JVM heap on short inputs, see #3464.
- Parenthesize membership-valued set-map bodies in `PrettyWriter` output so that SANY does not confuse them with map bindings.
- Correctly parenthesize prefix and prime expressions and negative integer literals in `PrettyWriter` output.
