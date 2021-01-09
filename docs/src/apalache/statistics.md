# TLA+ Anonymized Execution Statistics

Apalache participates in the optional [anonymized statistics programme] along
with [TLA+ Toolbox], TLC (which is part of the Toolbox), and [Visual Studio
Code Plugin for TLA+].

The statistics collection is **never enabled by default**. You have to **opt-in**
for the programme either in TLA+ Toolbox, or in Apalache. When statistics
collection is enabled by the user, it is submitted to `tlapl.us` via the
util.[ExecutionStatisticsCollector], which is part of `tla2tools.jar`. Apalache
accesses this class in at.forsyte.apalache.tla.[Tool].

As explained in [anonymized statistics programme], if you never create the file
`$HOME/.tlaplus/esc.txt`, then the statistics is not submitted to `tlapl.us`.
If you opt-in for the programme and later remove the file, then the statistics
will not be submitted too.


## Why do we ask you to help us

There are several reasons:

  - Although our project is open source, developing Apalache is our main job.
    We are grateful to [Informal Systems] for supporting us and to [TU Wien],
    [Vienna Science and Technology Fund], and [Inria Nancy/LORIA], who
    supported us in the past.  It is easier to convince our decision makers to
    continue the development, if we have clear feedback on how many people
    **use and need Apalache**.

  - We would like to know which features you are using most, so we can focus on
    them.

  - We would like to know which operating systems and Java versions need care
    and better be included in automated test suites.

## How to opt-in and opt-out

To opt-in in the statistics collection, execute the following command:

```sh
./apalache-mc config --enable-stats=true
```

As a result of this command, a random identifier is written in
`$HOME/.tlaplus/esc.txt`. This identifier is used by the execution statistics
code.

To opt-out from the statistics collection, execute the following command:

```sh
./apalache-mc config --enable-stats=false
```

## What exactly is submitted to tlapl.us

You can check the daily log at [exec-stats.tlapl.us](https://exec-stats.tlapl.us/).

The following data is submitted for each run, if you have opted in:

  - Total number of CPU cores and cores assigned
  (the latter is 1 for now, but will change soon)
  - Java heap memory size (in Megabytes)
  - Apalache version (semantic version + build)
  - Command mode: `parse`, `check`, or `typecheck`
  - Name, version, and architecture of the OS
  - Vendor, version, and architecture of JVM
  - Timestamp + salt (a random number to make time less precise)
  - An installation ID that is stored in `$HOME/.tlaplus/esc.txt`


[TLA+ Toolbox]: http://lamport.azurewebsites.net/tla/toolbox.html
[Visual Studio Code Plugin for TLA+]: https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus
[anonymized statistics programme]: https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/util/ExecutionStatisticsCollector.md
[ExecutionStatisticsCollector]: https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/util/ExecutionStatisticsCollector.java
[Tool]: https://github.com/informalsystems/apalache/blob/unstable/mod-tool/src/main/scala/at/forsyte/apalache/tla/Tool.scala
[Informal Systems]: https://informal.systems
[TU Wien]: https://www.tuwien.at/
[Vienna Science and Technology Fund]: https://www.wwtf.at/index.php?lang=EN
[Inria Nancy/LORIA]: https://www.inria.fr/en/centre-inria-nancy-grand-est
