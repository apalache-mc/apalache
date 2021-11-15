# ADR-008: Apalache Outputs

| author                   | revision |
|--------------------------|---------:|
| Jure Kukovec, Shon Feder |        2 |

This ADR documents the various files produced by Apalache, and where they get written to.

## 1. Categories of outputs
Files produced by Apalache belong to one of the following categories:

  1. Counterexamples 
  2. Log files
  3. Intermediate state outputs
  4. Run analysis files

Counterexamples (if there are any) and basic logs should always be produced, but the remaining outputs are considered optional. 
Each optional category is associated with a flag: `--write-intermediate` for intermediate state outputs and an individual flag for each kind of analysis. At the time of writing, the only analysis is governed by `--profiling`, for profiling results. 
All such optional flags should default to `false`.

## 2. Output directory and run directories
Apalache should define an `out-dir` parameter, which defines the location of all outputs produced by Apalache. If unspecified, this value should default to the working directory, during each run, but it should be possible to designate a fixed location, e.g. `<HOME>/apalache-out/`.

Each run looks for a subdirectory inside of the `out-dir` with the same name as
the principle file provided as input (or, for commands that do not read input
from a file, named after the executed subcommand). This subdirectory is called
the specification's (resp. command's) *namespace* within the `out-dir`.  All
outputs originating from that input file (resp. command) will be written to this
namespace.

Each run produces a subdirectory in its namespace, with the following name:

```
<DATE>T<TIME>_<UNIQUEID>
```

based on the [ISO 8601](https://en.wikipedia.org/wiki/ISO_8601) standard.
Here, `<DATE>` is the date in `YYYY-MM-DD` format, `<TIME>` is the local time in `HH-MM-SS` format.

Example file structure for a run executed on a file `test.tla`:

```
_apalache-out/
└── test.tla
    ├── 2021-11-05T22-54-55_810261790529975561
```

### Custom run directories

The `--run-dir` flag can be used to specify an output directory into which
outputs are written directly. When the `--run-dir` flag is specified, all
content included in the run directory specified above will *also* be written
into the directories specified by this argument.

## 3. Structure of a run directory

Each run directory outlined in the previous section, should contain the
following:
  
- A file `run.txt`, containing the command issued for this run, with all implicit parameters filled in, so it can be replicated exactly
- 0 or more counterexample files
- if `--write-intermediate` is set, a subdirectory `intermediate`, containing outputs associated with each of the passes in Apalache
- an Apalache log file `detailed.log`.
- an SMT log file `log0.smt`
- Files associated with enabled analyses, e.g. `profile-rules.txt`

## 4. Global Configuration File

Apalache should define a global configuration file `apalache-global-config`, e.g. in the `<HOME>/.tlaplus` directory, in which users can define the default values of all parameters, including all flags listed in section 1, as well as `out-dir`. The format of the configuration file is an implementation detail and will not be specified here.
If a parameter is specified in the configuration file, it replaces the default value, but specifying a parameter manually always overrides config defaults.
In other words, parameter values are determined in the following way, by order of priority:
  1. If `--<flag>=<value>` is given, use `<value>`, otherwise
  2. If `apalache-global-config` specifies `<flag>=<CFGvalue>` use `<CFGvalue>`, otherwise 
  3. Use Apalache defaults.

## 5. Output files

Some commands write specific files that are used to communicate with other
programs. E.g., 

- `parse` writes files with the results of parsing the input spec
- `check` writes counterexamples used by MBT

To facilitate programmatic use of this data, such commands also take an
`--output=<FILE>` flag, and then write the relevant output to the given file.
These output files are usually not in the `out-dir`.

The format for the output files is determined by the extension of the specified
file. E.g., `--output=foo.json` should result in JSON being written to file
`foo.json` (if supported for the command).
