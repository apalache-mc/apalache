# ADR-009: Server Mode

TODO:

- [x] Review the github discussion to gather requirements
- [ ] Read adr-3
- [ ] Review source code, to see current state of TransitionExecutor
    - [ ] Find point at which executor gets called by the checker
- [ ] Sketch a denotational model of the domain
- [ ] Syntax for the language to manipulate domain
- [ ] Write up design

## Requirements

- allows exploring model checking of a spec without overhead of JVM startup
  and apalache preprocessing (https://github.com/informalsystems/apalache/issues/730#issue-855835332)
- serves model-checking queries 
- extensible to support LSP
- can load and unload specs (https://github.com/informalsystems/apalache/issues/730#issuecomment-818201654)
- extensible for cloud-based usage
- extensible for interactive terminal usage
- exposes symbolic model checking (https://github.com/informalsystems/apalache/issues/730#issue-855835332)
  - can incrementally advance steps
  - can incrementally rollback steps
  - can incrementally change choice points
  - supports enumerating counterexamples
  - supports enumerating parameter values that lead to counterexample (https://github.com/informalsystems/apalache/issues/79#issuecomment-576449107)

## Aim

```ocaml
type tla_exp
type smt
type translater = tla_exp -> smt
type transition_exec = translater -> checker 
```

Checker 

## Protocol

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
