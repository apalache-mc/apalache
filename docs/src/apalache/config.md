# Apalache configuration

Apalache configuration files use **strict JSON**. The supported filenames are
`.apalache.json` for a project file and `$HOME/.tlaplus/apalache.json` for a user-wide file.

## Loading and precedence

Values are applied in this order, from highest to lowest precedence:

1. command-line arguments;
2. environment variables used by command-line options;
3. the file passed with `--config-file`, or the nearest `.apalache.json` found by searching the current directory and
   its parents;
4. `$HOME/.tlaplus/apalache.json`;
5. built-in defaults.

An explicit `--config-file` disables the search for a local file, but not the global fallback. Lists and ordinary values
replace lower-precedence values.
`checker.tuning` objects are merged by key.

The old `.apalache.cfg` and `$HOME/.tlaplus/apalache.cfg` application configuration filenames are rejected, even when
they contain valid JSON or a
`.json` file exists beside them. Rename them to `.apalache.json` and
`$HOME/.tlaplus/apalache.json`, respectively. Explicit `--config-file` paths ending in `.cfg` are rejected as well.
HOCON syntax is no longer supported.

This does not affect TLC configuration files passed with `--config`, which files conventionally use the `.cfg`
extension.

## JSON rules

Configuration must be one JSON object. Keys and strings require double quotes. The following constructs are
**rejected**: Comments, substitutions such as `${PWD}`, unquoted keys, `=`, trailing commas, duplicate keys, and
trailing documents. **Unknown keys are rejected** in every group; for example, `checker.discardDisabled`
is an error.

`source` and `output` are top-level values. The former `input` object and object-valued `output` section are rejected.

A leading `~` or `~/` in a path expands to the user's home directory. Other environment-variable expansion is not
performed.

This is a complete, copyable example:

```json
{
   "out-dir": "./_apalache-out",
   "debug": false,
   "smtprof": false,
   "write-intermediate": false,
   "profiling": false,
   "features": [],
   "source": "./Spec.tla",
   "output": "./Parsed.tla",
   "checker": {
      "algo": "incremental",
      "discard-disabled": true,
      "length": 10,
      "max-error": 1,
      "timeout-smt": 0,
      "no-deadlock": false,
      "smt-solver": "z3",
      "smt-encoding": "oopsla19",
      "tuning": {}
   },
   "typechecker": {
      "infer-poly": true
   },
   "server": {
      "port": 8822,
      "server-type": "checker"
   }
}
```

## Supported keys

An absent default of “none” means that the value is genuinely optional.

| Group         | Key                  | Description                                                  | JSON type                    | Default / values                            |
|---------------|----------------------|--------------------------------------------------------------|------------------------------|---------------------------------------------|
| top level     | `out-dir`            | Base directory for generated run directories.                | path string                  | `./_apalache-out`                           |
|               | `run-dir`            | Also write this run's output directly to this directory.     | path string                  | none                                        |
|               | `debug`              | Enable detailed logging and a configuration snapshot.        | boolean                      | `false`                                     |
|               | `smtprof`            | Write an SMT constraint profile.                             | boolean                      | `false`                                     |
|               | `write-intermediate` | Save intermediate representations produced by passes.        | boolean                      | `false`                                     |
|               | `profiling`          | Write profiling data for transformation rules.               | boolean                      | `false`                                     |
|               | `features`           | Enable experimental language or checker features.            | array of strings             | `[]`; names shown by CLI help               |
|               | `source`             | Select the specification file or in-memory source.           | path string or source object | required by modes that read a specification |
|               | `output`             | Write the processed module to this file.                     | path string                  | none; `.tla` and `.json` are supported      |
| `checker`     | `tuning`             | Set advanced checker and solver parameters.                  | object of string values      | `{}`                                        |
|               | `algo`               | Select the model-checking algorithm.                         | string                       | `incremental`; also `offline`, `remote`     |
|               | `config`             | Read behavior and properties from a TLC configuration file.  | path string                  | none                                        |
|               | `discard-disabled`   | Pre-check and discard disabled transitions.                  | boolean                      | `true`                                      |
|               | `cinit`              | Name the operator that initializes constants.                | string                       | none                                        |
|               | `init`               | Name the operator that initializes variables.                | string                       | `Init`, unless supplied by a TLC file       |
|               | `inv`                | Name the invariant operators to check.                       | array of strings             | `[]`, unless supplied by a TLC file         |
|               | `next`               | Name the transition operator.                                | string                       | `Next`, unless supplied by a TLC file       |
|               | `length`             | Limit the number of `Next` steps explored.                   | integer                      | `10`                                        |
|               | `max-error`          | Limit the number of reported counterexamples.                | integer                      | `1`; values above 1 require `view`          |
|               | `timeout-smt`        | Limit the duration of each SMT query.                        | integer seconds              | `0` (unlimited)                             |
|               | `no-deadlock`        | Disable deadlock checking when set to `true`.                | boolean                      | `false`                                     |
|               | `smt-solver`         | Select the SMT solver backend.                               | string                       | `z3`; also `cvc5`                           |
|               | `smt-encoding`       | Select the SMT encoding.                                     | string                       | `oopsla19`; also `arrays`, `funArrays`      |
|               | `temporal`           | Name the temporal properties to check.                       | array of strings             | `[]`, unless supplied by a TLC file         |
|               | `view`               | Name the operator used to project states in counterexamples. | string                       | none                                        |
| `typechecker` | `infer-poly`         | Allow inference of polymorphic types.                        | boolean                      | `true`                                      |
| `tracee`      | `trace`              | Select the trace to evaluate.                                | path string or source object | required by `tracee`; ITF or Apalache JSON  |
|               | `expressions`        | Name the expressions evaluated in each trace state.          | nonempty array of strings    | required by `tracee`                        |
| `server`      | `port`               | Set the listening port.                                      | integer                      | `8822`                                      |
|               | `server-type`        | Select the server implementation.                            | string                       | `checker`; also `explorer`                  |

Top-level `command` and `config-file` can appear in JSON exchanged with the RPC API and in diagnostic snapshots. Normal
configuration files should not set them; the selected command and `--config-file` provide those values.

A file source is normally just a path string. RPC callers may provide an in-memory source:

```json
{
   "source": {
      "kind": "string",
      "content": "---- MODULE M ----\n====",
      "aux": [],
      "format": "tla"
   }
}
```

The source formats are `tla`, `json`, `itf`, and `qnt`. A file with a nonstandard or ambiguous extension can use a
source object with
`"kind": "file"`, `"path": "..."`, and an explicit `"format"`.

## TLC configuration precedence

For `init`, `next`, `inv`, `temporal`, and deadlock checking, an application configuration value overrides the TLC file.
Otherwise the TLC value is used, then the application default. `CHECK_DEADLOCK FALSE` is equivalent to
`"no-deadlock": true`.

## Deprecated JSON aliases

The following old spellings remain accepted with warnings:

| Deprecated                | Canonical                |
|---------------------------|--------------------------|
| `checker.timeout-smt-sec` | `checker.timeout-smt`    |
| `checker.no-deadlocks`    | `checker.no-deadlock`    |
| `checker.temporal-props`  | `checker.temporal`       |
| `typechecker.inferpoly`   | `typechecker.infer-poly` |

Old object-shaped enum and source values using a `type` field are also read with a warning. Setting a canonical key and
its alias together is an error.

## Migrating from HOCON

Change HOCON such as:

```text
common {
  run-dir = ~/apalache-run
}
```

to JSON:

```json
{
   "run-dir": "~/apalache-run"
}
```

Then rename `.apalache.cfg` to `.apalache.json` before running Apalache; legacy application configuration filenames are
errors. With `--debug`, the merged canonical JSON configuration is written to `application-config.json` in the run
directory.
