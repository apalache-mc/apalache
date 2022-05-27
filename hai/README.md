# Hai: Human-Apalache Interaction

## What Hai is

Hai is a component of Apalache dedicated to supporting interaction with the
symbolic model checker.

### Services

- **TransEX**:  Interactively drive the Apalache
  [`TransitionExecutor`](../tla/bmcmt/trex/TransitionExecutor.scala) via remote
  procedure calls (RPCs).

## Why it's called Hai

'Hai' is an initialism of "Human-Apalache Interaction" and happily also carries
[a bunch of other connotations](https://en.wiktionary.org/wiki/hai).

## How Hai works

This project implements a server allowing clients to interact with Apalache. 

The server is implemented using the
[ZIO-gRPC](https://scalapb.github.io/zio-grpc/) stack. And the RPC messages are
defined using protobuf.

To learn the basic's of ZIO approach to concurrency, see the [ZIO
overview](https://zio.dev/version-1.x/overview/).

The principle concepts are noted here:

### The effect type `ZIO[Env, Failure, Success]`

Values of type `ZIO[Env, Failure, Success]` represent concurrent effects which
execute with the environment `Env` and may produce either a value of type
`Failure` or value of type `Success`.

Common type alias we use in Hai include:

- `IO[Failure, Failure]`, which is an effect that can operate in any
  environment.

### Concurrent and sequential effects

Effects run concurrently by default. Given

``` scala
val foo: IO[Err, Int] = ZIO.succeed(expensiveComputation())
val bar: IO[Err, String] = ZIO.succeed(expensiveStringOperation())
```

the value `foo` and `bar` will be computed concurrently.

We can operate on `ZIO` values by `map`ping over them. So to add 1 to our
expensive computation:

``` scala
val fooPlusOne: IO[Err, Int] = foo.map(_ + 1)
```

We can sequence `ZIO` values by `flatMap`ping over them:

``` scala
val fooTwice: IO[Err, Int] = foo.flatMap(r => ZIO.succeed(expensiveComputation() + r))
```

But, more succinctly, we can use for comprehensions to sequence the operations:

``` scala
val sequenced: IO[Err, Int] = 
  for {
    r1 <- foo
    r2 <- foo
  } yield (r1 + r2)
```

The for comprehension yielding a value of type ZIO operates within a
computational context in which the concurrent effects are sequenced.

## How Hai is organized

### The API is versioned

Hai is currently at `v1`, which is defined in the package
`at.forsyte.apalache.hai.v1`. After the API is stabilized, when we make breaking
changes to it, well do so in a new subpackage.

### Protobuf specs generate the RPC interface

The [protobuf](https://developers.google.com/protocol-buffers/docs/proto3)
specifications live in [src/main/protobuf/](src/main/protobuf/).

When this project is compiled, via `sbt hai/compile`, Scala source code is
generated from the protobuf specs into
[./target/scala-2.13/src_managed/main/scalapb/](./target/scala-2.13/src_managed/main/scalapb/).


## Resources

- [Preliminary Design Notes](../docs/src/adr/010rfc-transition-explorer.md)
