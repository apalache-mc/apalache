## 0.30.0 - 2022-10-24

### Breaking changes

- The format of parsing error outputs has been changed. Parsing error messages that used to be prefixed with `Error by TLA+ parser` are now prefixed with `Parsing error` and error messages that used to begin with `Syntax error in annotation:` will now also include the `Parsing error` prefix. This is being recorded as a breaking change since it could break scripts that rely on parsing stdout. (See #2204 and #2242.)

### Features

- Return JSON with success or failure data from RPC calls to the CmdExecutor service (see #2186).

### Bug fixes

- Write the SMT log also to a custom rundir specified with `--run-dir=`, see #2208
