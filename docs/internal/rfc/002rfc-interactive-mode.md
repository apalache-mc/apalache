# RFC-002: Implementation of an Interactive Mode

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

## Proposal

### Overview

In the current architecture, there is a single mode of operation in which 

- the user invokes Apalache with an initial configuration,
- the model checker proper then drives the
  [TransitionExecutor](../../src/adr/003adr-trex.md) through symbolic executions
  that effect the verification of specified properties for the given model.

Let's call this mode of operation *automatic mode*. 

This RFC proposes the addition of an *interactive mode*. The interactive mode
will allow a client to interact with the various steps of the verification
process, effectively bypassing the checker, to drive the `TransitionExecutor`
interactively. The specific functionality that should be available for
interaction is listed in the [Requirements](#requirements).

As per [previous
discussions](https://github.com/informalsystems/apalache/issues/730#issue-855835332),
interaction will be supported by running a daemon (or "service") that serves
requests. Clients will interact via a simple, well supported protocol providing
an online RPC interface to client programs.

### Requirements

The follow requirements have been gathered through conversation and discussion
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

#### Protocol

## LSP 

### Alternatives discussed

- Custom protocol on top of HTTP
- JSON-rpc
- gRPC

I propose use of gRPC for the following reasons:

- It will automate most of the IO and protocol plumbing we'd have to do
  ourselves.
- It is battle tested by [industry](https://grpc.io/)
- It is already used in Rust projects within Informal Systems.
- The [Scala library](https://scalapb.github.io/docs/grpc/) appears to be well documented and actively maintained.
- [Official support](https://grpc.io/docs/languages/) in many popular languages,
  and we can expect well-maintained library support in most languages.

For a discussion of some comparison between JSON-rpc and gRPC, see

- https://www.mertech.com/blog/know-your-api-protocols
- https://stackoverflow.com/questions/58767467/what-the-difference-between-json-rpc-with-http2-vs-grpc

### Design

FRP?

We will use the [functional reactive programming][frp] (FRP) paradigm to
implement a [reactive program][]. This provides a clean and rigorously grounded
conceptual framework for organizing the interactions with Apalache, which is
friendly to Scala's functional bent, and appears to be well supported by existing libraries in
the ecosystem: 

https://medium.com/expedia-group-tech/fully-reactive-request-processing-with-project-reactor-grpc-and-mongodb-140991412360

[reactive programming]: https://en.wikipedia.org/wiki/Reactive_programming
[frp]: https://en.wikipedia.org/wiki/Functional_reactive_programming

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
