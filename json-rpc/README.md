# JSON-RPC Server for Apalache

**Authors:** [Igor Konnov][] and [Thomas Pani][]

A simple JSON-RPC server module for Apalache. This is work in progress:

This server is not meant to be a replacement for the current gRPC server (SHAI).
Rather, it is a lightweight alternative that can be used for symbolic
exploration of TLA+ specifications.

## 1. Design principles

- The server is designed for running on a local machine:
    - It does not do any load balancing. If you check plenty of specs in parallel,
      it may run out of memory.
    - It is not meant to face the Internet. An attacker may find a way to crash it.
      You should always run it behind a firewall.

- The server implementation is minimalistic:
    - It implements a small number of methods that are sufficient for symbolic
      exploration.
    - All advanced exploration techniques are implemented outside of this
      module, in third-party applications.
    - The server is language-agnostic, so it can be used with any programming
      language that supports JSON-RPC.

- The server must be easy to test:
    - The exploration logic is isolated in the `ExplorationService`, which
      does not depend on any Web technology.
    - The parsing logic is separated from the service logic, so it can be
      tested independently.
    - The server component is a simple servlet, which can be tested with
      anything like `curl`.
    - No fancy web frameworks are used.

- No rocket-science FP knowledge is required to understand and maintain the code.
  It's basic Scala and old-school Java.

- The server is powered by battle-tested technology, no fancy soopa-doopa Scala
  unsupported monadic frameworks:
    - [Jetty Server][]. Yes, it is about 30 years old.
      It works. It is fast, simple, reliable, maintained, and is well-documented.
    - [Jackson][]. It is fast, simple, reliable, maintained, and is well-documented.
      It uses plain-old Java objects, and it supports basic Scala types. No super-advanced
      FP here.

## 2. JSON-RPC methods

In the following, we only describe successful responses. If an error occurs,
the server will return a JSON object with the `error` field, which contains
the error code and message. The `id` field will be the same as in the request.
See the [JSON-RPC specification][] for more details. It is real short.

This is work in progress. More methods to be added in the future.

**Running the server.** To try the examples below, you need to start the server
first:

```sh
$ ../bin/apalache-mc server --server-type=explorer
```

### 2.1. Method loadSpec

Load a TLA+ specification from a list of base64-encoded source files.
The server will parse the specification and store all the necessary
objects in memory for further exploration. This includes the SMT solver.
The solver does not consume much memory after loading the specification.
However, it may consume a lot of memory when checking the specification
in the subsequent calls. Hence, you should be mindful of the memory
when loading multiple specifications in different sessions.

**Effect.** The server creates a new session and stores all the necessary
state in memory. The specification is loaded, parsed, type-checked,
preprocessed, etc. If there is a constant initializer, it is applied to the
SMT context. The server returns a unique session identifier, which should
be used in subsequent calls to refer to this session.

**Input:**

```json
{
  "method": "loadSpec",
  "params": {
    "sources": [
      <rootModuleInBase64>,
      <importedModule1InBase64>,
      ...
    ],
    "init": "optional-initializer-for-constants",
    "next": "optional-transition-predicate",
    "invariants": [
      "invariant 1",
      ...,
      "invariant N"
    ]
  }
}
```

**Output:**

```json
{
  "result": {
    "sessionId": "unique-session-identifier",
    "snapshotId": snapshot-identifier-after-loading-the-spec,
    "specParameters": {
      "nInitTransitions": number-of-Init-transitions,
      "nNextTransitions": number-of-Next-transitions,
      "nStateInvariants": number-of-state-invariants,
      "nActionInvariants": number-of-action-invariants,
      "nTraceInvariants": number-of-trace-invariants,
      "hasView": true-if-there-is-a-view-operator
    }
  }
}
```

The `sessionId` is a unique identifier for the session. You should use this
identifier in subsequent calls to the server to refer to the loaded specification.
The `snapshotId` is an identifier of the snapshot that was created after loading
the specification and initializing the constants, if there is a constant initializer.
Further, `specParameters` contains key parameters of the specification that are
usually needed for symbolic exploration.

**Example**:

Execute the following command:

```sh
$ SPEC=`cat <<EOF | base64
---- MODULE Inc ----
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == x = 0
Next == (x < 3 /\\ x' = x + 1) \\/ (x > -3 /\\ x' = x - 1)
Inv3 == x /= 0
\* @type: () => <<Bool, Bool, Bool>>;
View == <<x < 0, x = 0, x > 0>>
=====================
EOF`
curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"loadSpec","params":{"sources": [ "'${SPEC}'" ], "invariants": ["Inv3"], "view": "View"},"id":1}'
```

It should produce the following output:

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "sessionId": "1",
    "snapshotId": 0,
    "specParameters": {
      "nInitTransitions": 1,
      "nNextTransitions": 2,
      "nStateInvariants": 1,
      "nActionInvariants": 0,
      "nTraceInvariants": 0,
      "hasView": true
    }
  }
}
```

### 2.2. Method disposeSpec

Dispose the state that is associated with a session, including the SMT solver.
You should call this method when you are done with the session. The session
identifier must have been returned by the `loadSpec` method in an earlier call.

**Effect.** The server removes all the state that is associated with the
session identifier. No further calls should be made with this session identifier.

**Input:**

```json
{
  "method": "disposeSpec",
  "params": {
    "sessionId": "session-identifier"
  }
}
```

**Output:**

On success, the server returns the identifier of the disposed session.
This identifier cannot be used in the future calls.

```json
{
  "result": {
    "sessionId": "session-identifier"
  }
}
```

**Example**:

Execute the following command:

```sh
$ curl -X POST http://localhost:8822/rpc \
-H "Content-Type: application/json" \
-d '{"jsonrpc":"2.0","method":"disposeSpec","params":{"sessionId": "1"},"id":2}'
```

It produces an output like this:

```json
{"jsonrpc":"2.0","id":2,"result":{"sessionId":"1"}}
```

### 2.3. Method rollback

Rollback the context of a session to an earlier snapshot. The snapshot identifier
must have been returned by an earlier call.

**Precondition.** The `snapshotId` must have been returned earlier by another method.
In addition to that, if a snapshot $n$ was returned by a method with the sequence number $i$,
and the method `rollback` is called with `snapshotId` set to $m$ with the sequence number $j$,
then there must be no intermediate call to rollback with a snapshot $m < n$ with a sequence
number $k$ such that $i < k < j$.

**Effect.** The server rolls back the context of the session to the snapshot
with the given identifier $n$. All snapshots with identifiers greater than $n$ are
discarded. The snapshot with identifier $n$ remains in the server, so you can
roll back to it again later.

**Input:**

```json
{
  "method": "rollback",
  "params": {
    "sessionId": "session-id",
    "snapshotId": snapshot-id
  }
}
```

**Output:**

A successful rollback returns the session identifier and the snapshot identifier
that was rolled back to:

```json
{
  "result": {
    "sessionId": "session-id",
    "snapshotId": snapshot-id
  }
}
```


**Example**:

Execute the following command:

```sh
$ curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"rollback","params":{"sessionId":"1","snapshotId":0},"id":2}'
```

It produces the following output:

```json  
{"jsonrpc":"2.0","id":2,"result":{"sessionId":"1","snapshotId":0}}
```


### 2.4. Method assumeTransition

Given a session identifier and a transition identifier, prepare this transition in the
SMT context and assume that this transition holds true. Additionally, if `checkEnabled`
is set to `true`, the server checks, whether there is a state that is reachable via
the current transition prefix, including the supplied transition. The parameter `timeoutSec`
sets the timeout for this check in seconds. If `timeout` is not set, or it is set to `0`, then
the timeout is infinite.

**Precondition.** This method should be called once before calling `nextState`, unless
the previous call to `assumeTransition` returned with the status `"DISABLED"`.

**Effect.** The transition with `transitionId` is prepared in the SMT context, and the
corresponding constraints are added to the context. Unless the method returns with
the status `"DISABLED"`, the context remains modified after the call. If the method
returns with the status `"DISABLED"`, then the context is rolled back to the latest
snapshot.

**Input:**

```json
{
  "method": "assumeTransition",
  "params": {
    "sessionId": "session-identifier",
    "transitionId": transition-identifier,
    "checkEnabled": check-if-transition-is-enabled,
    "timeoutSec": timeout-in-seconds-or-0,
  }
}
```

**Output:**

```json
{
  "result": {
    "sessionId": "session-identifier",
    "snapshotId": new-snapshot-id,
    "transitionId": transition-identifier,
    "status": "ENABLED|DISABLED|UNKNOWN"
  }
}
```

**Example**:

Execute the following command:

```sh
$ curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"assumeTransition","params":{"sessionId":"1","transitionId":0,"checkEnabled":true},"id":2}'
```

It produces the following output:

```json  
{"jsonrpc":"2.0","id":2,"result":{"sessionId":"1","snapshotId":1,"transitionId":0,"status":"ENABLED"}}
```

### 2.5. Method nextState

Given a session identifier, switch to the next symbolic state. This method should be called
only after the `assumeTransition` method was called successfully (with the status `"ENABLED"`
or `"UNKNOWN"`).

**Precondition.** This method should be called after `assumeTransition` that returned with the status
`"ENABLED"` or `"UNKNOWN"`. If the last call to `assumeTransition` returned with the status
`"DISABLED"`, then `nextState` produces an error.

**Effect.** This method renamed the primed states variables such `x'` to unprimed variables
such as `x`. It does not add any new constraints to the SMT context. Hence, if the constraints
were satisfiable before the call, they remain satisfiable after the call. To accommodate for
new constraints, `nextStep` takes a new snapshot.

**Input:**

```json
{
  "method": "nextState",
  "params": {
    "sessionId": "session-identifier"
  }
}
```

**Output:**

```json
{
  "result": {
    "sessionId": "session-identifier",
    "snapshotId": new-snapshot-id,
    "newStepNo": new-step-number
  }
}
```

**Example**:

Execute the following command:

```sh
$ curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"nextStep","params":{"sessionId":"1"},"id":3}'
```

It produces the following output:

```json
{"jsonrpc":"2.0","id":5,"result":{"sessionId":"1","snapshotId":3,"newStepNo":1}}
```

### 2.6. Method checkInvariant

Given a session identifier and an invariant identifier, check whether this invariant can be violated
by a concrete execution that follows the collected symbolic path. The invariant identifier is a number
that follows the following rules:

- If `kind == "STATE"`, then `invariantId` refers to a state invariant.
  The following constraints must be satisfied: `0 <= invariantId` and `invariantId < nStateInvariants`.
- If `kind == "ACTION"`, then `invariantId` refers to an action invariant.
  The following constraints must be satisfied: `0 <= invariantId` and
  `invariantId < nActionInvariants`.
- If `kind` is not set, then `invariantId` refers to a state invariant.

The parameter `timeoutSec` sets the timeout for this check in seconds. If `timeout` is not set, or it is set to `0`,
then the timeout is infinite.

If the invariant is violated, then `invariantStatus` is set to `"VIOLATED"`, and the `trace` field contains a concrete
execution that violates the invariant. This field encodes a trace in the [ITF Format][].

**Precondition.** State invariants must be checked after `nextState`, and action
invariants must be checked between a call to `assumeTransition` and a subsequent
call to `nextState`.

**Effect.** This method temporarily changes the model checker context. After
checking the invariant, the context is rolled back to the state before the call.

**Input:**

```json
{
  "method": "checkInvariant",
  "params": {
    "sessionId": "session-identifier",
    "invariantId": invariant-identifier,
    "kind": "STATE|ACTION",
    "timeoutSec": timeout-in-seconds-or-0
  }
}
```

**Output:**

```json
{
  "result": {
    "sessionId": "session-identifier",
    "invariantStatus": "SATISFIED|VIOLATED|UNKNOWN",
    "trace": trace-in-itf-or-null,
  }
}
```

**Example**:

Execute the following command:

```sh
$ curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"checkInvariant","params":{"sessionId":"1","invariantId":0},"id":3}'
```

The output is as follows:

```json
{"jsonrpc":"2.0","id":5,"result":{"sessionId":"1","invariantStatus":"SATISFIED"}}
```

### 2.7. Method query

Given a session identifier, query the current context for values of several kinds:

 - `"TRACE"`: A concrete trace that follows the symbolic path constructed so far.
   There may be multiple such traces. This call returns the trace that
   was found by the SMT solver.
 - `"VIEW"`: The value of the view operator. The name of this operator must be
   specified in the `view` field of the `loadSpec` method. There may be multiple
   such values. This call returns the view of the model that was found by the
   SMT solver.
 - TBD: More kinds to be added in the future.

**Precondition.** No preconditions.

**Effect.** This method does expression evaluation internally. Hence, it checks
the satisfiability of the current context. Hence, multiple calls to `query` may
produce "garbage" in the SMT context. We believe that this should not affect
the performance of the solver. If you disagree with this, you can always roll
back to an earlier snapshot.

Some of the queries require an additional satisfiability check. The parameter
`timeoutSec` sets the timeout for this check in seconds. If `timeout` is not
set, or it is set to `0`, then the timeout is infinite.

**Input:**

```json
{
  "method": "query",
  "params": {
    "sessionId": "session-identifier",
    "kinds": [ kind1, kind2, ... ],
    "timeoutSec": timeout-in-seconds-or-0
  }
}
```

**Output:**

```json
{
  "result": {
    "sessionId": "session-identifier",
    "trace": trace-in-itf-or-null,
    "view": view-in-itf-or-null
  }
}
```

**Example**:

Execute the following command:

```sh
$ curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"query","params":{"sessionId":"1","kinds":["VIEW"]},"id":5}'
```

The output is as follows:

```json
{"jsonrpc":"2.0","id":5,"result":{"sessionId":"1","trace":null,"view":{"#tup":[false,true,false]}}}
```

### 2.8. Method nextView

**NOT IMPLEMENTED YET**

Given a session identifier, find a view that is different from the one in the
current context. This method requires a call to the SMT solver, so it may take
some time. The parameter `timeoutSec` sets the timeout for this check in seconds.
If `timeout` is not set, or it is set to `0`, then the timeout is infinite.
If `nextView` returns with the status `"SATISFIED"`, then the current context
has a model, and the view can be obtained by calling the `query` method.

**Precondition.** The `loadSpec` method must have been called with the parameter
`view`. This method is successful only if the current context has a model.
Otherwise, the result is undefined. For details, see the precondition of the
`query` method.

**Effect.** This method changes the SMT context. It adds a constraint that excludes
the current value of the view operator. To prevent this constraint from propagating
into the next states, once you are done with enumerating the views, you should
roll back to the snapshot before the first call to `nextView` (e.g., to the snapshot
returned by `nextState`).

**Input:**

```json
{
  "method": "nextView",
  "params": {
    "sessionId": "session-identifier",
    "timeoutSec": timeout-in-seconds-or-0
  }
}
```

**Output:**

```json
{
  "result": {
    "sessionId": "session-identifier",
    "status": (SATISFIED|VIOLATED|UNKNOWN)
  }
}
```

**Example**:

Execute the following command:

```sh
$ curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"nextView","params":{"sessionId":"1","timeoutSec":10},"id":6}'
```

The output is as follows:

```json
TODO
```

[Jetty Server]: https://jetty.org/

[Jackson]: https://github.com/FasterXML/jackson

[JSON-RPC specification]: https://www.jsonrpc.org/specification

[Igor Konnov]: https://konnov.phd

[Thomas Pani]: https://thpani.net

[ITF Format]: https://apalache-mc.org/docs/adr/015adr-trace.html