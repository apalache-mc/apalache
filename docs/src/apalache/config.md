# Apalache configuration file
Apalache allows you to specify certain parameters, governing outputs produced by it, as described in [ADR-009](../adr/009adr-outputs.md).

You can create a file named `apalache.cfg` in `$HOME/.tlaplus/` and populate it with values for the following flags:
  - `OUTDIR`: The value of `OUTDIR` defines a directory, in which all Apalache runs write their outputs. Each run will produce a unique subdirectory inside `OUTDIR` using the following convention: `<SPECNAME>_yyyy-MM-dd_HH-mm-ss_<UNIQUEID>`. 
  Example value: `~/apalache-out`.
  If this value is not defined in `apalache.cfg`, Apalache will, for each individual run, define it to be equal to `DIR/x/`, where `DIR` is the directory containing the specification.
  - `profiling`: This Boolean flag has to be one of `TRUE/true/FALSE/false` and governs the creation of `profile-rules.txt` used in [profiling](profiling.md). The file is only created if `profiling` is set to `TRUE/true`. Avoid using the `--smtprof` flag when `profiling` is set to `FALSE/false`.
  If this value is not defined in `apalache.cfg` it is treated as `false`.
  - `write-intermediate`: This Boolean flag has to be one of `TRUE/true/FALSE/false` and governs the creation of intermediate outputs. If set to `TRUE/true`, apalache will produce an `intermediate` subdirectory in the run directory and output the state of the module after each pass.
  If this value is not defined in `apalache.cfg` it is treated as `false`.

All flags must be defined on separate lines, and follow the pattern
```
FLAGNAME=FLAGVALUE
```

Example of a valid `apalache.cfg`:
```
OUTDIR=~/apalache-out
profiling=true
write-intermediate=true
```
