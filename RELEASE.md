## 0.62.0 - 2026-08-18

### Breaking changes

- Raised the minimum supported Java runtime from Java 17 to Java 21.
- `OutputManager` state is now scoped to each `Tool.run` invocation; direct callers must use `OutputManager.withScope`, and asynchronous callers must propagate a captured scope.
