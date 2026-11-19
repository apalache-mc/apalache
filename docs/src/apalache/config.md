# Apalache configuration

Apalache configuration files use **strict JSON**. The supported filenames are
`.apalache.json` for a project file and `${user.home}/.tlaplus/apalache.json` for a user-wide file, where `user.home`
is the JVM user-home system property.

## Loading and precedence

The following sources are considered, in decreasing order of precedence:

1. command-line arguments;
2. environment variables used by command-line options;
3. at most one selected configuration file;
4. built-in defaults.

The configuration file is selected by taking the first applicable choice:

1. the file passed with `--config-file`, or a path supplied through its `CONFIG_FILE` environment variable;
2. `.apalache.json` in the current working directory;
3. `${user.home}/.tlaplus/apalache.json`;
4. no configuration file.

Apalache previously supported `.cfg` configuration files in HOCON syntax, as well as recursive merging of configuration
files. These are no longer supported.

The above rules to do not apply to the TLC configuration files passed with `--config`.

## JSON rules

Configuration must be one JSON object. Keys and strings require double quotes. The following constructs are
**rejected**: Comments, substitutions such as `${PWD}`, unquoted keys, `=`, trailing commas, duplicate keys, and
trailing documents. **Unknown keys are rejected** in every group; for example, `checker.discardDisabled`
is an error. Moreover, `source` and `output` are top-level values. The former `input` object and object-valued `output`
section are rejected. Deprecated aliases and object-form enum values are not accepted.

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

In the table below, a default of "none" means that the value is optional.

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

Top-level `command` and `config-file` can appear in trusted JSON and configuration dumps when in debug mode.
Normal configuration files should not set them; the selected command and `--config-file` provide those values.
Remote RPC configuration rejects `config-file`.

A file source is normally just a path string. RPC callers must provide an in-memory source:

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

### Remote RPC configuration

Remote request JSON is parsed without configuration-file discovery. The fields `config-file`, `out-dir`, `run-dir`,
`output`, and `checker.config` are rejected, as are file-backed `source` and `tracee.trace` values. In-memory source
content and auxiliary modules remain supported. In-memory TLA+ modules can import only supplied auxiliary modules and
trusted standard modules, not modules from the server's working directory.

The following Z3 tuning keys are also rejected for remote requests, as they can create files:

- `z3.dot_proof_file`,
- `z3.trace`,
- `z3.trace_file_name`,
- `z3.sat.drat.file`,
- `z3.sat.inprocess.out`,
- `z3.solver.axioms2files`,
- `z3.solver.cancel_backup_file`,
- `z3.solver.proof.log`,
- `z3.solver.smtlib2_log`,
- `z3.opt.dump_benchmarks`,
- `z3.opt.solution_prefix`,
- `z3.smt.arith.dump_lemmas`.

Default output files are still produced by the services.

## TLC configuration precedence

For `init`, `next`, `inv`, `temporal`, and deadlock checking, an application configuration value overrides the TLC file.
Otherwise the TLC value is used, then the application default. `CHECK_DEADLOCK FALSE` is equivalent to
`"no-deadlock": true`.

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

Then rename `.apalache.cfg` to `.apalache.json` before running Apalache. Automatically discovered legacy filenames are
ignored, while an explicit `--config-file` ending in `.cfg` is an error. With `--debug`, the merged canonical JSON
configuration is written to `config.json` in the run directory.

The strict JSON parser accepts only canonical names and values. In particular, apply these changes to older
configurations:

| Former representation              | Canonical JSON           |
|------------------------------------|--------------------------|
| `input.source`                     | top-level `source`       |
| `checker.timeout-smt-sec`          | `checker.timeout-smt`    |
| `checker.no-deadlocks`             | `checker.no-deadlock`    |
| `checker.temporal-props`           | `checker.temporal`       |
| `typechecker.inferpoly`            | `typechecker.infer-poly` |
| source field `type`                | source field `kind`      |
| source field `file`                | source field `path`      |
| `filesource`/`stringsource`        | `file`/`string`          |
| `fun-arrays`/`oopsla-19`           | `funArrays`/`oopsla19`   |
| `checker-server`/`explorer-server` | `checker`/`explorer`     |

Enum values are JSON strings, not objects containing a `type` field.
