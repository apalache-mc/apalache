# RFC-002: Implementation of Transition Exploration Server

## Problem

Users of Apalache have voiced a need for the following general behaviors:

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

|TRANS-EX.1::QCHECK.1|
: enable checking specs without repeated JVM startup costs
  (https://github.com/informalsystems/apalache/issues/730#issue-855835332)

|TRANS-EX.1::EXPLORE.1|
: enable exploring model checking results for a spec without repeated
  preprocessing costs
  (https://github.com/informalsystems/apalache/issues/730#issue-855835332) 

|TRANS-EX.1::LOAD.1| 
: can load and unload specs
  (https://github.com/informalsystems/apalache/issues/730#issuecomment-818201654)

|TRANS-EX.1::EXTENSIBLE.1|
: The transition explorer should be extensible in the following ways:

    |TRANS-EX.1::EXTENSIBLE.1::CLOUD.1| 
    : extensible for cloud-based usage

    |TRANS-EX.1::EXTENSIBLE.1::LSP.1| 
    : extensible for LSP support

    |TRANS-EX.1::EXTENSIBLE.1::CLI.1| 
    : extensible for interactive terminal usage |

|TRANS-EX.1::SBMC.1|
: exposes symbolic model checking (https://github.com/informalsystems/apalache/issues/730#issue-855835332)

    |TRANS-EX.1::SBMC.1::ADVANCE.1|
    : can incrementally advance steps

    |TRANS-EX.1::SBMC.1::ROLLBACK.1|
    : can incrementally rollback steps

    |TRANS-EX.1::SBMC.1::TRANSITIONS.1|
    : sends data on available transitions

    |TRANS-EX.1::SBMC.1::SELECT.1|
    : receives selection to execute specific transition

    |TRANS-EX.1::SBMC.1::COUNTER.1|
    : supports enumerating counterexamples
      (https://github.com/informalsystems/apalache/issues/79#issue-534407916)
    
    |TRANS-EX.1::SBMC.1::PARAMS.1|
    : supports enumerating parameter values (`CONSTANTS`) that lead to a
      counterexample
      (https://github.com/informalsystems/apalache/issues/79#issuecomment-576449107)


### Architecture

Interactive mode will take advantage of the `TransitionExecutor`'s "nice
abstraction to write different model checking strategies".

I propose the following high-level architecture:

- Use an RPC protocol to allow client and server mutually transparent
  interaction. (This allows us to abstract away the communication protocol and
  only consider the functional API in what follows.)
- Introduce a new module, `ServerModule`, into the `apa-tool` package, to bind
  the relevant passes, which lead up to, and terminate with, the 
  `TransitionExplorer`, described below.
- Introduce a new module, `TransitionExplorer` that abstracts over the 

*NOTE*: The high-level sketch above assumes the new code organization proposed
in [ADR 7][].

[ADR 7]: https://github.com/informalsystems/apalache/tree/unstable/docs/src/adr/007adr-restructuring.md

#### API

The following is a rough sketch of the proposed API for the transition explorer.
It attempts to give a highly abstracted interface, but in terms of existing data
structures. Naturally, refinements and alterations are to be expected during
implementation.

```scala

/** A state is a map from variables to values  */
type StateMap = Map[TlaEx, TlaEx]

/** An execution is an alternating sequence of states and actions
 *  terminating with a state */
type Execution = List[Either[StateMap, TlaEx]]

trait TransitionExplorer {

  /** Reset the state of the explorer
   *
   * Returns the explorer to a state as if the currently loaded model where
   * freshly loaded. Used to restart exploration from a clean slate.
   * 
   * [TRANS-EX.1::LOAD.1]
   */

  def reset(): Unit
  
  /** Load a model for exploration
   *
   * If a model is already loaded, it will be replaced and the state of the exploration
   * [[reset]].
   *
   * [TRANS-EX.1::QCHECK.1]
   * [TRANS-EX.1::LOAD.1]
   * 
   * @param spec the TLA+ specification defining the
   * @return `Left(LoadErr)` if parsing or loading the model from `spec` goes
   *          wrong, or `Right(())` if the model is loaded successfully.
   */
  def loadModel(spec: String): Either[LoadErr, Unit]
  
  /**  The root module currently loaded in memory  */
  def loadedModel: Option[TlaModule]

  /** The initial states of the model
   *
   * Since the number of computable initial states can be infinite, an upper
   * limit must be set.
   * 
   * @params max the maximum number of initial states to return (default to 100)
   * @params start the nth state to begin fetching from (defaults to 0)
   * @return `Some(exprs)` where `exprs` are `n` computed initial states, with
   *         `n` <= `max`, or `None` if no model is loaded.
   */
  def initialStates(max: Int = 100, start: Int = 0): Option[TlaEx]

  /**  The initial state predicates given in the spec  */
  def initialStatePredicates: Option[TlaEx]

  /** The "next" state transitions given in the spec
   *
   * Since the number of computable transitions can be infinite, an upper
   * limit must be set.
   * 
   * @params max the maximum number of initial states to return (default to 100)
   * @params start the nth state to begin fetching from (defaults to 0)
   * @return `Some(exprs)` where `exprs` are `n` computed initial states, with
   *         `n` <= `max`, or `None` if no model is loaded.
   */
  def nextTransitionPredicates: Option[TlaEx]

  def invariants: Option[CheckerInputVC]

  /** Setting constants will also reset the explorer */
  def initializeConstants(Map[TlaExp, TlaExp]): Either[LoadErr, Unit]

  /** Gives a map of constants to their current values   */
  def constants: Option[Map[TlaEx, Option[TlaEx]]]

  /** The current state, as a map from variables to values */
  def currentState: Option[StateMap]

  /**  The next state achieved by applying a transition non-deterministically
   *
   * [TRANS-EX.1::SBMC.1::ADVANCE.1]
   * 
   * @return `Left[err]` if the checker encounters an error, or Right[]  */
  def nextState(): Either[CheckErr, StateMap]

  /**  Step the exploration back to the previous state
   * 
   * [TRANS-EX.1::SBMC.1::ROLLBACK.1]
   * 
   */
  def previousState(): Either[CheckErr, StateMap]

  /** The actions that can be applied to the current state
   *
   * [TRANS-EX.1::SBMC.1::TRANSITIONS.1]
   * 
   */
  def enabledActions(): Option[List[TlaEx]]

  /** The next state, achieved by applying the given action
   *
   * |TRANS-EX.1::SBMC.1::SELECT.1|
   * 
   */
  def applyAction(action: TlaEx): Either[CheckErr, StateMap]

  /** The execution from the selected initial state up to the [[currentState]]  */
  def executionFragment: Option[Execution]

  /** Enumerate counter examples based on an execution
   * 
   * [TRANS-EX.1::SBMC.1::COUNTER.1]
   * 
   */
  def enumerateCounterExamples(
    execution: Execution,
    max: Int = 100,
    start: Int = 0
  ): List[TlaEx]

  /** Enumerate counter examples based on partitioning of state space
   *
   * [TRANS-EX.1::SBMC.1::COUNTER.1]
   * 
   * NOTE: The mechanics of this are currently unclear to me.
   */
  def enumerateCounterExamplesByState(
    partialState: StateMap,
    otherState: StateMap,
    max: Int = 100,
    start: Int = 0
  ): List[TlaEx]
}
```

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

I have asked internally, and engineers on both `tendermint-rs` and `hermes` have
vouched for the ease of use and reliability of gRPC.

Using gRPC can help satisfy [TRANS-EX.1::EXTENSIBLE.1] in the following ways:

- [TRANS-EX.1::EXTENSIBLE.1::CLOUD.1] should be satisfied out of the box, since
  HTTP is the default transport for gRPC.
- [TRANS-EX.1::EXTENSIBLE.1::CLI.1] can be satisfied by implementing a CLI
  client that we can launch via an Apalache subcommand.
- [TRANS-EX.1::EXTENSIBLE.1::LSP.1] is not directly enabled, but it should not
  be blocked either. 
