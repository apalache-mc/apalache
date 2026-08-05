## 0.59.0 - 2026-08-05

### Breaking changes

- Configuration files now can be stored in `.apalache.json` or `${user.home}/.tlaplus/apalache.json`, in strict JSON. HOCON `.cfg` files are no longer supported. The JSON structure is simplified. Check the manual for details. See PR #3409.

### Features

- Publish the `tla-ir` and `tla-io` Scala libraries under the `org.apalache-mc` Maven Central namespace.

### Bug fixes

- Fixed an unsoundness where folding over an infinite set such as `Nat` or `Int` (e.g. `ApaFoldSet(Op, v, Nat)`) silently treated the set as empty and returned the base value. Apalache now reports a clear "known limitation" error instead, see #1691.

### Documentation

- Add ADR026: Explicit configuration and command options
