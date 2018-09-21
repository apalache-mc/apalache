# APALACHE project

Abstraction-based parameterized TLA+ checker [![Build Status](https://travis-ci.org/konnov/apalache.svg?branch=master)](https://travis-ci.org/konnov/apalache)

The current version of the tool is neither parameterized, nor it is using
abstractions. As a first step, we are working on a symbolic bounded model
checker that runs under the same assumptions as TLC. To see the list of supported TLA+ constructs, check the [supported features page](./features.md).

Related reports and publications can be found at the
[apalache page](http://forsyte.at/research/apalache/).

## Releases

Check the [releases page](https://github.com/konnov/apalache/releases).
As the tool is in the early development stage, there are a few releases. 

To try the latest features, you can download
[the latest unstable build](https://github.com/konnov/apalache/releases/tag/latest-unstable).

## Running the binaries

First, make sure that you have installed [Oracle JRE 8](https://www.oracle.com/technetwork/java/javase/downloads/jre8-downloads-2133155.html)
(or JDK8) and [Microsoft Z3 4.7.1](https://github.com/Z3Prover/z3/releases/tag/z3-4.7.1).

The model checker can be run as follows:

```bash
$ bin/apalache-mc check --init=Init --next=Next --inv=Inv --length=10 myspec.tla
```

The tool will display only the important messages. A detailed log can be found in `detailed.log`.

In contrast to TLC, the tool assumes that all specification parameters are
fixed right in the specification. We will add support for TLC models in
the future.

## Building from sources

To build the tool, you will need the following standard packages: Java 8 SDK,
Scala, and Maven. You will also need [Z3 Prover
4.7.1](https://github.com/Z3Prover/z3) and [TLA tools](http://lamport.azurewebsites.net/tla/tools.html).
Both Z3 and TLA+ tools can
be automatically installed in your local Maven repository by running the script
`./3rdparty/install-local.sh`. __WARNING: Z3 API has been changed in version
4.8.0, so make sure that you install version 4.7.1.__

To build the complete package, including the dependencies, type:

```bash
$ mvn package
```

