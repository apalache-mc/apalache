# ADR-008: Apalache Outputs

| author     | revision |
| ------------ | --------:|
| Jure Kukovec |    1 |

This ADR documents the various files produced by Apalache, and where they get written to.

## 1. Categories of outputs
Files produced by Apalache belong to one of the following categories:

  1. Counterexamples 
  2. Log files
  3. Intermediate state outputs
  4. Run analysis files

Counterexamples (if there are any) and basic logs should always be produced, but the remaining outputs are considered optional. 
Each optional category is associated with a flag: `--debug` for extended log files, `--write-intermediate` for intermediate state outputs and an individual flag for each kind of analysis. At the time of writing, the only analysis is governed by `--profiling`, for profiling results. 
All such optional flags should default to `false`.

## 2. Output directory and run directories
Apalache should define an `OUTPUT_DIR` value, which defines the location of all outputs produced by Apalache. If unspecified, this value should default to the directory, in which the primary specification is located during each run, but it should be possible to designate a fixed location, e.g. `<HOME>/apalache-out/`.

Each run should produce a subdirectory in `OUTPUT_DIR`, with the following name:
```
<DATE>_<TIME>
```

based on the [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) standard.
Here, `<DATE>` is the date in `YYYY-MM-DD` format, `<TIME>` is the local time in `HH-MM-SS` format.

Example:
```
2021-05-02_21-31-59
```
for a run executed on May 2, 2021 at 9:31:59pm (local time).

## 3. Structure of a run directory

Each run directory, outlined in the previous section, should contain the following:
  
  - A file `run.txt`, containing the command issued for this run, e.g.:
  ```
  check --inv=SomeInv Spec.tla
  ```
    alternatively (DISCUSS), the file could contain the full command, with all implicit parameters filled in, so it can be replicated exactly
  - 0 or more counterexample files
  - if `--write-intermediate` is set, a subdirectory `intermediate`, containing outputs associated with each of the passes in Apalache
  - an Apalache log file `detailed.log`. If `--debug` is set, the log file contains `DEBUG` level events, in addition to the regular ones
  - an SMT log file `log0.smt`
  - A file associated with enabled analyses, e.g. `profile-rules.txt`

## 4. Master CONFIG
Apalache should define a master configuration file `apalache.cfg`, e.g. in the installation directory, in which users can define the default values of all parameters, including all flags listed in section 1, as well as `OUTPUT_DIR`.
If a parameter is specified in the config file, it replaces the default value, but specifying a parameter manually always overrides config defaults.
In other words, parameter values are determined in the following way, by order of priority:
  1. If `--<flag>=<value>` is given, use `<value>`, otherwise
  2. If `apalache.cfg` specifies `<flag>=<CFGvalue>` use `<CFGvalue>`, otherwise 
  3. Use Apalache defaults.

