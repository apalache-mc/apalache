# Shai: Server for Human-Apalache Interaction

## What Shai is

Shai is a component of Apalache dedicated to supporting human interaction with
the symbolic model checker.

### Services

- **TransEX**:  Interactively drive the Apalache
  [`TransitionExecutor`](../tla/bmcmt/trex/TransitionExecutor.scala) via remote
  procedure calls (RPCs).

## Why it's called Shai

'Shai' is an initialism of "Server for Human-Apalache Interaction" and carries
[a few other connotations you could consider][shai]. It's pronounced "shy".

[shai]: https://en.wiktionary.org/wiki/shai

## How Shai works

This project implements a server allowing clients to interact with Apalache. 

The server is implemented on top of
[ZIO-gRPC](https://scalapb.github.io/zio-grpc/) stack.

To learn the basic's of ZIO approach to concurrency, see the [ZIO
overview](https://zio.dev/version-1.x/overview/).  The principle concepts are
noted here:

### The effect type `ZIO[Env, Failure, Success]`

ZIO is a concurrency library that works by lifting effects into typed values,
and then running a scheduler that can execute the effects concurrently and in
parallel, as appropriate given the available resources and context.

In order for ZIO to track effects, every effect (i.e. side-effects) must be
lifted into ZIO values. If we execute side-effects without lifting them into ZIO
values, they will escape the scheduler, and we lose the ability to reason about
or manage the effects. The basic combinators for lifting effects into ZIO values
are `ZIO.effect` and `ZIO.effectTotal`. The former is for effects that may abort
with some exception. The latter is for effects which are guaranteed to complete.

Values of type `ZIO[Environment, Failure, Success]` represent concurrent effects
which execute within an environment tracked by a value of type `Environment`,
and which may produce either a value of type `Failure` or value of type
`Success`. The `Environment` supplies requirements that the effect may need
(e.g., resources to interact with the outside world).

Common type aliases we use in Shai include:

- `IO[Failure, Succcess]`: an effect that can operate in any environment.
- `UIO[Success]`: an effect that always succeeds

### Concurrent and sequential effects

Effects run concurrently, by default. I.e., given

``` scala
val foo: IO[Err, Int] = ZIO.succeed(expensiveComputation())
val bar: IO[Err, String] = ZIO.succeed(expensiveStringOperation())
```

the value `foo` and `bar` will be computed concurrently (at the discretion of
ZIO's scheduler, and we just don't worry about this).

We can operate on the success values of effects by `map`ping over them. So to
add 1 to our expensive computation:

``` scala
val fooPlusOne: IO[Err, Int] = foo.map(_ + 1)
```

We can sequence effects by `flatMap`ping over them:

``` scala
val fooTwice: IO[Err, Int] = foo.flatMap(r => ZIO.succeed(expensiveComputation() + r))
```

More succinctly, we can use `for` comprehensions to sequence the operations:

``` scala
val sequenced: IO[Err, Int] = 
  for {
    r1 <- foo // Block until foo is computed and return the success value
    r2 <- foo // Block until foo is computed and return the success value
  } yield (r1 + r2) // The success value to be returned
```

A `for` comprehension yielding a value into `ZIO` establishes a computational
context in which effects are evaluated sequentially and their successful 
values can be inspected.

## How Shai is organized

### The API is versioned

Shai is currently at `v1`, which is defined in the package
`at.forsyte.apalache.shai.v1`. After the API is stabilized, whenever we make
breaking changes to it, we'll do that in a new subpackage. This will allow us to
expose the latest developments in the model checker to our users without
requiring them to adapt to an API that is a moving target.

### The RPC interface is generated from protobuf specs

The [protobuf](https://developers.google.com/protocol-buffers/docs/proto3)
specifications live in [src/main/protobuf/](src/main/protobuf/).

When this project is compiled, via `sbt shai/compile`, Scala source code is
generated from the protobuf specs into
[./target/scala-2.13/src_managed/main/scalapb/](./target/scala-2.13/src_managed/main/scalapb/).

### Services are registered with the `RpcServer`

The source code for the sever and services lives in
[src/main/scala/at/forsyte/apalache/shai/](src/main/scala/at/forsyte/apalache/shai/).

Related functionality is grouped into services, defined in supporting files, and
then the services are registered with the
[`RpcServer`](src/main/scala/at/forsyte/apalache/shai/rpcServer.scala).

## Tests

We use the `zio-test` library as the principle test harness for this project.

You may find it useful to consult the following documentation:

- [Overview](https://zio.dev/version-1.x/usecases/usecases_testing/)
- [Documentation](https://zio.dev/version-1.x/howto/test-effects)
- [Tutorial](https://scala.monster/zio-test/)
- [Tutorial on shared dependencies](https://hmemcpy.com/2021/11/working-with-shared-dependencies-in-zio-test/)

## Resources

- [Preliminary Design Notes](../docs/src/adr/010rfc-transition-explorer.md)
