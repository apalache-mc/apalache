# ADR-013: Configuration Management Component

| authors                                | last revised    |
| -------------------------------------- | --------------: |
| Shon Feder                             | 2022-08-15      |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

<!-- Statement to summarize, following the following formula: -->

In the context of using Apalache from other programs, different environments, and
in different planned modes (see, e.g., [#703][703]),\
facing the need to supply different configurations for different use cases\
we decided for adopting the [PureConfig][] library and for introducing a small component to
integrate `PureConfig` with our CLI parsing \
in order to achieve maintainable, reasonable, and extensible management of configurations\
accepting the additional external dependency and development costs.

[703]: https://github.com/apalache-mc/apalache/issues/730

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->

As our application grows more flexible, gains more adoption and usage in
programmatic pipelines, and strives to provide more functionality, we inevitably
need to make it more configurable.

Recent additions that have extended configurability include:

- [#1081](https://github.com/apalache-mc/apalache/pull/1081), introducing
  the `run-dir` flag.
- [#1036](https://github.com/apalache-mc/apalache/pull/1036), introducing
  the `write-intermediate`, and `profiling`, `out-dir` configuration parameters,
  exposed both via CLI and configuration file.
- [#1054](https://github.com/apalache-mc/apalache/pull/1054), introducing
  the `smt-encoding` flag.
  
The ongoing work for [the server
mode](https://github.com/apalache-mc/apalache/issues/730) is expected to
require introducing several more configurable paramters.

As discussed in [#1069](https://github.com/apalache-mc/apalache/issues/1069)
and [#1929](https://github.com/apalache-mc/apalache/issues/1929) we have at
least 5 different sources from which we need to load configuration parameters,
and the loading must cascade, with the first listed source taking priority:

- CLI arguments **OR** data supplied by RPC
- environment variables
- A local configuration files (perhaps with the location overridden by a CLI
  flag)
- A global configuration 
- Predetermined defaults

We are currently managing this configuration in an ad hoc way, with a bespoke
configuration loading system, and various ad hoc methods for effecting
overrides.

## Options

<!-- Communicate the options considered.
     This records evidence of our consideration and the various alternatives
     considered.
-->

The problem can be decomposed into three parts:

1. Reading parameters from CLI and environment variables (currently done through
   our CLI library).
2. Reading parameters from configuration files (currently done in an ad hoc way)
3. Cascade loading these paramters in the correct order, to end up with the
   correct intended configuration.

To address (2) and (3), we should use an existing configuration management
library, since this will save us development time, and allow us to take
advantage of other developer's careful engineering around this problem, freeing
us to focus on our core problem domain.

There are some configuration libraries that aim to provide an integrated
solutions to all three problems, but I have dismissed them for reasons described
below.


### Comparison of configuration management libraries

I considered four actively maintained libraries focused on application
configuration. This section reports my findings.

#### Activity

| Library        | Contributors | Last Release | GitHub Stars | Build Status |
|:---------------|:-------------|:-------------|--------------|--------------|
| [config][]     | 89           | 2020-10-22   | 5.5k         | passing      |
| [profig][]     | 5            | 2021-01-14   | 23           | failing      |
| [metaconfig][] | 23           | 2021-05-31   | 29           | passing      |
| [PureConfig][] | 58           | 2021-11-21   | 1.2k         | passing      |


#### Features

| Library        | Formats                                 | File Merging | Envvar Fallback | CLI Arg Merging | Language | Typing  | Documentation |
|:---------------|:----------------------------------------|:-------------|-----------------|-----------------|----------|---------|---------------|
| [config][]     | java properties, JSON, HOCON            | yes          | yes             | manual          | Java     | dynamic | excellent     |
| [profig][]     | java properties, JSON, YAML, HOCON, XML | yes          | yes             | automatic       | Scala    | dynamic | decent        |
| [metaconfig][] | JSON, HOCON                             | ?            | ?               | automatic       | Scala    | static  | poor          |
| [PureConfig][] | java properties, JSON, HOCON            | yes          | semi            | automatic       | Scala    | static  | excellent     |
 
#### Additional notes

- [conifg][]
  - Integrates with Guice
  - Lots of support due to Java usage
- [profig][]
  - only apparent advantage over [config][] is automatic CLI parsing, but that
    also requires swapping out our CLI library.
- [metaconfig][]
  - Automatically generates markdown CLI documentation
  - Reports errors with location in configuration source
  - Treats CLI args just as another source for configuration data 
  - Maintained by [scalameta](https://github.com/scalameta)
  - Used by [scalafix](https://github.com/scalacenter/scalafix) and scalafmt
- [PureConfig][]
  - Type safe wrapper around [config][], so should inherit all features of that
    basis (including Guice integration)
  - Will automatically merge configs based on a priority list of files.
  - Support optional configuration fallback
  - Supports writing out configs (can be used in bug reports or populating
    default config to help guide users)

### Evaluation

I discount [profig][] because it has nothing significant to recommend it over [config][].

[metaconfig][] is attractive due its support for type safe configuration,
generation of markdown documentation, but the poor documentation and relatively
small user base counts against it. Those other factors are not sufficiently
attractive to outweigh the risks.

The choice between [config][] and [PureConfig][] is easy: [PureConfig][]
includes everything provided by [config][], but exposes a types safe,
Scala-native API. Moreover, it's got a substantial user-base and excellent
documentation.

[profig]: https://github.com/outr/profig
[config]: https://github.com/lightbend/config
[metaconfig]: https://github.com/scalameta/metaconfig
[PureConfig]: https://github.com/pureconfig/pureconfig

## Solution

We will adopt [PureConfig][] as our configuration management library. It will
enable us to cascade load configuration files from many exernal sources
(including a json blob passed in via CLI inputs) and provide type-safe access to
the configured values.

We will continue to rely on `clist` for CLI parsing for the time being, which
takes care of loading environment variable settings and CLI arguments with our
desired overriding precedence. This will require we add a thin abstraction that
will ensure the CLI arguments end up overriding the configured values. This
abstraction will replace the more ad hoc process we are currently employing to
this end.

Here's a short example of how basic usage should look (approximately), allowing
us to replace dozens of lines of code in the `OutputManager` implementing our
current adhoc configuration parsing:


```scala
import pureconfig._
import pureconfig.generic.auto._

// Setting a defaul value
case class Port(number: Int = 8080) extends AnyVal

sealed trait SmtEncoding
case class Arrays extends SmtEncoding
case class OOPSLA19 extends SmtEncoding

case class ApalacheConfig(
  runDir: Option[Path] = None,
  serverPort: Port = Port(),
  writeIntermediate: Boolean = false,
  profiling: Boolean = false,
  outDir: Path = Path("."),
  smtEncding: SmtEncoding = OOPSLA19,
)

case classs ExampleUseOfConfigs() = {
  val cli = CliParseResults()
  val localConfig = ConfigSource.file(Path.cwd.resolve(".aplache.config"))
  val globalConfig = ConfigSource.file(ApalacheHome.resolve("apalache.config"))
  val loadedConfig: ConfigReader.Result[ApalacheConfig] = globalConfig
    .withFallback(localConfig)
    .load[ApalacheConfig]

  // Finally, override with CLI arguments
  // Unfortunatley, I've not found a robust way to automate this yet
  val config = loadedConfig.copy(
    runDir = cli.runDir.getOrElse(loadedConfig.runDir),
    serverPort = cli.runDir.getOrElse(loadedConfig.serverPort),
    // etc..
  )

}
```

This `ApalacheConfig` class can then be passed around to all parts of the
program that need to read such configurations.

## Consequences

After utilizing the approach proposed here for nearly a year, we were able to
introduce several additional configurations easily, and we found the local
configuration files useful for tweaking program behavior. We subsequently
decided to further extend the configuration system by integrating the CLI within
the configuration system and use it as the basis for statically representing all
program options. See [ADR 022](./022adr-unification-of-configs-and-options.md).
