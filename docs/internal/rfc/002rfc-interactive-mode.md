# RFC-002: Implementation of Transition Exploration Server

TODO:

- [x] Review the github discussion to gather requirements
- [x] Read adr-3
- [ ] Review source code, to see current state of TransitionExecutor
    - [ ] Find point at which executor gets called by the checker
- [ ] Sketch denotational design
  - [ ] Maybe - Sketch a denotational model of the domain
  - [ ] Maybe - Syntax for the language to manipulate domain
- [ ] Write up design

## Problem

Users of Apalache have voiced a need for the following behaviors:

- incremental results (that can be iterated to exhaustively enumerate all counterexamples)
- interactive selection of checking strategies
- interactive selection of parameter values

The discussion around these needs is summarized and linked from 
https://github.com/informalsystems/apalache/issues/79 .

The upshot is this: we can provide value by adding a utility that will allow
users to interactively and incrementally explore the transition systems defined
by a given TLA+ spec.

## Proposal

### Overview

In the current architecture, there is a single mode of operation in which 

- the user invokes Apalache with an initial configuration,
- and the model checker proper then drives the
  [TransitionExecutor](../../src/adr/003adr-trex.md) through symbolic executions
  that effect the verification of specified properties for the given model.

This RFC proposes the addition of an *transition exploration server*. The server
will allow a client to interact with the various steps of the verification
process, effectively bypassing the checker, to drive the `TransitionExecutor`
interactively. The specific functionality that should be available for
interaction is listed in the [Requirements](#requirements).

As per [previous
discussions](https://github.com/informalsystems/apalache/issues/730#issue-855835332),
interaction will be supported by running a daemon (or "service") that serves
requests. Clients will interact via a simple, well supported protocol providing
an online RPC interface to client programs.

As a followup, we can create our own front-end client to interact with this
server, perhaps as a simple web application.

### Requirements

The following requirements have been gathered through conversation and discussion
on our GitHub issues:

1. enable checking specs without repeated JVM startup costs
  (https://github.com/informalsystems/apalache/issues/730#issue-855835332)
2. enable exploring model checking results for a spec without repeated
  preprocessing costs
  (https://github.com/informalsystems/apalache/issues/730#issue-855835332) 
3. can load and unload specs (https://github.com/informalsystems/apalache/issues/730#issuecomment-818201654)
4. extensible for cloud-based usage
5. extensible for LSP support
6. extensible for interactive terminal usage
7. exposes symbolic model checking (https://github.com/informalsystems/apalache/issues/730#issue-855835332)

   (i) can incrementally advance steps
   (ii) can incrementally rollback steps
   (iii) sends data on available transitions
   (iv) receives selection to execute specific transition
   (v) supports enumerating counterexamples
   (vi) supports enumerating parameter values (`CONSTANTS`) that lead to a counterexample (https://github.com/informalsystems/apalache/issues/79#issuecomment-576449107)


### Architecture

Interactive mode will take advantage of the `TransitionExecutor`'s "nice
abstraction to write different model checking strategies".

I propose the following high-level architecture:

- Use an RPC protocol to allow client and server mutually transparent
  interaction. (This allows us to abstract away the communication protocol and
  only consider the functional API in what follows.)
- Introduce a new module, `ServerModule`, into the `apa-tool` package, which
  will provide an abstraction over the `TransitionExecutor` in `apa-base`

*NOTE*: This sketch assumes the new code organization proposed in [ADR 7]( https://github.com/informalsystems/apalache/tree/unstable/docs/src/adr/007adr-restructuring.md).

#### API

~/Sync/informal-systems/apalache/apalache-core/tla-bmcmt/src/main/scala/at/forsyte/apalache/tla/bmcmt/trex/TransitionExecutorImpl.scala

https://github.com/informalsystems/apalache/tree/9e64fd2f1cccc5584524b3f3e884a64355abd64d/docs/src/adr/007adr-restructuring.md

#### Protocol

We have briefly discussed the following options:

- Custom protocol on top of HTTP
- JSON-rpc
- gRPC

I propose use of gRPC for the following reasons:

- It will automate most of the IO and protocol plumbing we'd otherwise have to
  do ourselves.
- It is battle tested by [industry](https://grpc.io/)
- It is already used in Rust projects within Informal Systems. This should make
  it easier to integrate into modelator.
- The [Scala library](https://scalapb.github.io/docs/grpc/) appears to be well
  documented and actively maintained.
- [Official support](https://grpc.io/docs/languages/) is provided in many
  popular languages, and we can expect well-maintained library support in most
  languages.
- The gRPC libraries include both the RPC protocol and plumbing for the
  transport layer, and these are decomposable, in case we end up wanting to use
  different transport (i.e., sockets) or a different protocol for some purpose
  down the line.

For a discussion of some comparison between JSON-rpc and gRPC, see

- https://www.mertech.com/blog/know-your-api-protocols
- https://stackoverflow.com/questions/58767467/what-the-difference-between-json-rpc-with-http2-vs-grpc

### Phases

- Take current checker module, but instead of running it, start a server, a process queries to the transition executor (specified in ADR3)
- Let's also bake in support for LSP protocol support.
- Should also feed into online use
- Should feed into REPL usage?
- RPC into the transition executor ADR
  - Gives us more incrementality
  - Will let us roll back and take different steps
  - Let's us expose the "symbolic execution" functionality
    - We're actually doing symbolic execution, but even more powerfully than many applications (because we explore branches)
- Aim is to avoid adding too m
- Let's aim for a deep API
- Symbolic model checking is very easy, in a sense.
  - Not so much to it.
  - Once we have the translation into SMT, the model checking is simple.
- Recalling the DFS mode we had before
