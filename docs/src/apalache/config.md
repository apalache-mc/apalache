# Apalache global configuration file
Apalache allows you to specify certain parameters, governing outputs produced by it, as described in [ADR-009](../adr/009adr-outputs.md).

You can create a global configuration file named `apalache-global-config.yml` in `$HOME/.tlaplus/` and populate it with values for the following flags, in YAML format:
  - `out-dir` (String): The value of `out-dir` defines a path to the directory,
  in which all Apalache runs write their outputs. Each run will produce a unique
  subdirectory inside `out-dir` using the following convention:
  `<SPECNAME>_yyyy-MM-dd_HH-mm-ss_<UNIQUEID>`. The use of `~` in the path
  specification is permitted. The directory path need not already exist.
  Example value: `'~/apalache-out'`.
  If this value is not defined in `apalache-global-config.yml`, Apalache will, for each individual run, define it to be equal to `CWD/_apalache-out/`, where `CWD` is the current working directory.
  - `profiling` (Bool): This flag governs the creation of `profile-rules.txt` used in [profiling](profiling.md). The file is only created if `profiling` is set to `True`.  Setting `profiling` to `False` is incompatible with the `--smtprof` flag.
  The default is `False`.
  - `write-intermediate` (Bool): This Boolean flag governs the creation of intermediate outputs. If set to `True`, apalache will produce an `intermediate` subdirectory in the run directory and output the state of the module after each pass.
  The default is `False`.


Example of a valid `apalache-global-config.yml`:
```
out-dir: '~/apalache-out'
profiling: True
write-intermediate: True
```
