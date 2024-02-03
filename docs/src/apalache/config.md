# Apalache configuration

Apalache supports configuration of some parameters governing its behavior.

Application configuration is loaded from the following four sources:

1. Command line arguments
2. Environment variables
3. A local configuration file
4. The global configuration file

The order of precedence of the sources follows their numbering: i.e., and any
configuration set in an earlier numbered source overrides a configuration set in
a later numbered source.

## Command line arguments and environment variables

To view the available command line arguments, run Apalache with the `--help`
flag and consult the section on [Running the Tool](./running.md) for more
details.

*Some* parameters configurable via the command line are also configurable via environment
variables. These parameters are noted in the CLI's inline help. If a parameter
is configured both through a CLI argument and an environment variable, then the
CLI argument always takes precedence. 

## Configuration files

### File format and supported parameters

Local configuration files support JSON and the JSON superset
[HOCON](https://github.com/lightbend/config/blob/master/HOCON.md).

Here's an example of a valid configuration for commonly used
parameters, along with their default values:

```yaml
common  {
    # Directory in which to write all log files and records of each run
    out-dir = "${PWD}/_apalache-out"

    # Whether or not to write additional files, that report on intermediate
    # processing steps
    write-intermediate = false

    # Whether or not to write general profiling data into the `out-dir`
    profiling = false

    # Fixed directory into which generated files are written (absent by default)
    # run-dir = ~/my-run-dir
}
```

A `~` found at the beginning of a file path will be expanded into the value set for
the user's home directory.

Details on the effect of these parameters can be found in [Running the
Tool](./running.md).

### Local configuration file

You can specify a local configuration file explicitly via the `config-file`
command line argument. If this is not provided, then Apalache will look for the
nearest `.apalache.cfg` file, beginning in the current working directory and
searching up through its parents.

Parameters configured in the local configuration file will be overridden by
values set via CLI arguments or environment variables, and will override
parameters configured via the global configuration file.

### Global configuration file

The final fallback for configuration parameters is the global configuration file
named `$HOME/.tlaplus/apalache.cfg`.
