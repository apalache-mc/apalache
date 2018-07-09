# APALACHE project

Abstraction-based parameterized TLA+ checker [![Build Status](https://travis-ci.org/konnov/apalache.svg?branch=master)](https://travis-ci.org/konnov/apalache)

Related reports and publications can be found at the
[apalache page](http://forsyte.at/research/apalache/).

## Building and running

To build the tool, you will need the following standard packages: Java 8 SDK,
Scala, and Maven.  You will also need [Z3 Prover](https://github.com/Z3Prover/z3)
and [TLA tools](http://lamport.azurewebsites.net/tla/tools.html).
Both can be automatically installed in your local Maven repository by running the
script `./3rdparty/install-local.sh`.

To build the complete package, including the dependencies, type:

```bash
$ mvn package
```

The model checker can be run as follows:

```bash
$ java -jar mod-distribution/target/distribution-0.1-SNAPSHOT-jar-with-dependencies.jar \
  check --init=Init --next=Next --inv=Inv --length=10 myspec.tla
```

In contrast to TLC, the tool assumes that all specification parameters are
fixed right in the specification. We will add support for TLC models in
the future.
