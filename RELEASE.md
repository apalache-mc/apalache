## 0.51.0 - 2025-11-06

### Features

- - Sort relations in the counterexamples (#3182)
- - Printing labels in the TLA+ counterexamples
- - Add `JVM_GC_ARGS` and default GC settings in `apalache-mc` (#3185)
- - Add `prompts/type-annotation-assistant.md` for AI-assisted type    annotations (#3194)
- Translate `val __label_Foo = true; e` in Quint to `Foo:: e` in TLA+ (#3168)
- - Process and print labels in transitions and invariants (#3167)

### Bug fixes

- - Fix the type aliases parser to allow for digits (#3199)
- - Fix the JSON-RPC method `query` to call `sat` first (#3205)
- - Stable order on the transitions as produced with assignment finder (#3198)
- - Fix transitive inlining of polymorphic Quint definitions (#3207)
