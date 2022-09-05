## 0.28.1 - 2022-09-05

### Breaking changes

- Invalid configuration keys found in configuration sources (e.g., `apalache.cfg` files) will now produce a configuration error on load (see #2125).
- The structure of the apalache.cfg has changed. All configuration keys that were previously supported have been moved under the `common` key. You can update your config files by prefixing each key from the previous versions with `commong.key-name`. For an example config file, see https://apalache.informal.systems/docs/apalache/config.html#file-format-and-supported-parameters. See #2065.
- Introduce --features=no-rows for the old record syntax and switch to `--features=rows` by default

### Features

- The application configuration is now dumped into the `run-dir` when the `--debug` flag is supplied (see #2134).
- All CLI parameters can now be configured via `apalache.cfg` files. See #2065 and documentation to follow.
- From now on, the type checker reports an error, when the inferred type is more specific than the annotated type, see #2109.
- The options `--init` and `--temporal` can now be given lists of names separated by commas, enabling users to check multiple invariants and temporal properties via the CLI (see #2074).
