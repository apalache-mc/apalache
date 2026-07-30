# Configuration and run options

This package owns Apalache's configuration model, merge semantics, validation, and mode-specific runtime options. JSON
parsing lives here, in
[ApalacheConfigJsonParser.scala]. Configuration-file discovery and precedence loading live in
[ApalacheConfigLoader.scala].

## Data flow

```text
CLI primary config + at most one selected JSON file (ApalacheConfigLoader)
        |
        v
ApalacheConfigJsonParser + mergeWithLower --> merged ApalacheConfig
        |
        v
ApalacheConfigResolver.resolve*
        |
        v
mode-specific Validated*Options
        |
        v
passes and services
```

`ApalacheConfig` is the top-level configuration. Its `source` and `output`
values are direct fields; grouped settings implement `ConfigPatch`. Both are deliberately sparse: `None` means that a
source did not provide the value.
`higher.mergeWithLower(lower)` applies precedence without adding defaults. Most fields replace the lower-precedence
value; `checker.tuning` is merged by key.

`ApalacheConfigResolver` is the boundary from sparse configuration to validated runtime values. It applies defaults,
loads TLC configuration where required, checks cross-field constraints, and returns the smallest option type needed by
the selected mode. Execution passes should consume these resolved types rather than interpret patches themselves.

For CLI execution, [Tool.scala] calls `toConfig`, selects at most one configuration file, and passes the merged
`ApalacheConfig` to the command. Commands must not cache or reload configuration. Untrusted service JSON is parsed and
checked by `RemoteConfigValidator` without invoking `ApalacheConfigLoader`. Both the JSON reader and writer use only
canonical names and representations.

Validated command types also expose `source` and `output` directly.
`ModuleIoOptions` is only the two-field adapter used by Guice when constructing frontend passes.

## Files

| File                             | Responsibility                                                                                        |
|----------------------------------|-------------------------------------------------------------------------------------------------------|
| [ApalacheConfig.scala]           | Top-level configuration data model, explicit merge rules, and defaults used for diagnostic snapshots. |
| [ApalacheConfigLoader.scala]     | Single-file selection, loading, and precedence merging.                                               |
| [ApalacheConfigResolver.scala]   | Defaults, TLC integration, validation, and construction of run options.                               |
| [ApalacheConfigJsonParser.scala] | Strict JSON decoding and canonical JSON writing.                                                      |
| [RemoteConfigValidator.scala]    | Filesystem-free validation for untrusted service request configuration.                               |
| [ConfigPatch.scala]              | Shared patch marker and sparse section patch types.                                                   |
| [Constants.scala]                | Shared configuration keys, command names, and canonical literal values.                               |
| [ValidatedOptions.scala]         | Immutable, validated values consumed during execution.                                                |
| [ConfigParseResult.scala]        | Expected configuration errors and warnings as values.                                                 |
| [ConfigEnums.scala]              | Closed sets of supported algorithms, solvers, encodings, and server types.                            |

## Maintenance rules

- Preserve absence in patches. Normal defaults belong in
  `ApalacheConfig.defaults`; `ApalacheConfigResolver` and diagnostic output consume them through `mergeWithDefaults`.
  Context-dependent defaults, such as values loaded from a TLC configuration, remain in the resolver.
- CLI commands must leave omitted options absent. Each subclass builds a sparse
  `ApalacheConfig` and merges it over its superclass configuration through
  [ApalacheCommand.scala].
- Keep merge code explicit. Avoid reflection and generic derivation so adding a field produces compiler-visible work and
  exceptional rules remain obvious.
- Report invalid user configuration through `ConfigParseResult`, not exceptions.
- Define external names once in `Constants`; JSON, CLI, and service boundaries must reuse them. Internal fields use
  descriptive Scala names.
- Boundary code may retain an `ApalacheConfig` while awaiting request-specific values, but passes should receive
  resolved run options.

## Adding an option

1. Add the sparse field to `ApalacheConfig` or the appropriate `*Patch`.
2. Add its explicit merge rule.
3. Add its external name to `Constants`, then decode and encode it in `ApalacheConfigJsonParser`. Update the CLI or RPC
   producer if applicable.
4. Add the runtime field, default, and validation in `ApalacheConfigResolver`.
5. Update consumers and tests for decoding, precedence, validation, and the relevant command.
6. Document the JSON key in `docs/src/apalache/config.md`.

[ApalacheConfig.scala]: ApalacheConfig.scala
[ApalacheConfigJsonParser.scala]: ApalacheConfigJsonParser.scala
[ApalacheConfigLoader.scala]: ApalacheConfigLoader.scala
[ApalacheConfigResolver.scala]: ApalacheConfigResolver.scala
[ApalacheCommand.scala]: ../../../../../../../../../mod-tool/src/main/scala/at/forsyte/apalache/tla/tooling/opt/ApalacheCommand.scala
[ConfigEnums.scala]: ConfigEnums.scala
[ConfigParseResult.scala]: ConfigParseResult.scala
[ConfigPatch.scala]: ConfigPatch.scala
[Constants.scala]: Constants.scala
[ValidatedOptions.scala]: ValidatedOptions.scala
[RemoteConfigValidator.scala]: RemoteConfigValidator.scala
[Tool.scala]: ../../../../../../../../../mod-tool/src/main/scala/at/forsyte/apalache/tla/Tool.scala
