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

### 2.1. Method loadSpec

Load a TLA+ specification from a list of base64-encoded source files.
The server will parse the specification and store all the necessary
objects in memory for further exploration. This includes the SMT solver.
The solver does not consume much memory after loading the specification.
However, it may consume a lot of memory when checking the specification
in the subsequent calls. Hence, you should be mindful of the memory
when loading multiple specifications in different sessions.

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

```sh
SPEC=`cat <<EOF | base64
---- MODULE Inc ----
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == x = 0
Next == (x < 3 /\\ x' = x + 1) \\/ (x > -3 /\\ x' = x - 1)
Inv3 == x /= 0
=====================
EOF`
curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"loadSpec","params":{"sources": [ "'${SPEC}'" ], "invariants": ["Inv3"]},"id":1}' 2>/dev/null | jq
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
      "hasView": false
    }
  }
}
```

### 2.2. Method disposeSpec

Dispose the state that is associated with a session, including the SMT solver.
You should call this method when you are done with the session. The session
identifier must have been returned by the `loadSpec` method in an earlier call.

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

```sh
curl -X POST http://localhost:8822/rpc \
-H "Content-Type: application/json" \
-d '{"jsonrpc":"2.0","method":"disposeSpec","params":{"sessionId": "1"},"id":2}'
```

### 2.3. Method assumeTransition

Given a session identifier and a transition identifier, prepare this transition in the
SMT context and assume that this transition holds true. Additionally, if `checkEnabled`
is set to `true`, the server checks, whether there is a state that is reachable via
the current transition prefix, including the supplied transition. The parameter `timeoutSec`
sets the timeout for this check in seconds. If `timeout` is not set, or it is set to `0`, then
the timeout is infinite.

To avoid an additional call, we also allow `assumeTransition` to roll back the context
to an earlier snapshot *before* assuming the transition. In this case, the `snapshotId` parameter
must be set to the identifier of the snapshot to roll back to. If `snapshotId` is negative
(or not set), then no rollback is performed.

**Input:**

```json
{
  "method": "assumeTransition",
  "params": {
    "sessionId": "session-identifier",
    "snapshotId": optional-snapshot-identifier,
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
    "snapshotId": snapshot-identifier-after-assuming-transition,
    "transitionId": transition-identifier,
    "status": "ENABLED|DISABLED|UNKNOWN"
  }
}
```

**Example**:

```sh
curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"assumeTransition","params":{"sessionId":"1","transitionId":0,"checkEnabled":true},"id":2}'
{"jsonrpc":"2.0","id":2,"result":{"sessionId":"1","snapshotId":1,"transitionId":0,"status":"ENABLED"}}
```

### 2.4. Method nextState

Given a session identifier, switch to the next symbolic state. This method should be called
only after the `assumeTransition` method was called successfully (with the status `"ENABLED"`
or `"UNKNOWN"`).

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
    "snapshotId": snapshot-id-after-assuming-transition,
    "newStepNo": new-step-number
  }
}
```

**Example**:

```sh
curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"nextStep","params":{"sessionId":"1"},"id":3}'
{"jsonrpc":"2.0","id":5,"result":{"sessionId":"1","snapshotId":3,"newStepNo":1}}
```

### 2.5. Method checkInvariant

Given a session identifier and an invariant identifier, check whether this invariant can be violated
by a concrete execution that follows the collected symbolic path. The invariant identifier is a number
that follows the following rules:

- If `0 <= invariantId < nStateInvariants`, then the identifier refers to a state invariant.
- If `nStateInvariants <= invariantId` and `nStateInvariants + nActionInvariants`, then the identifier refers to the
  action invariant `invariantId - nStateInvariants`.

The parameter `timeoutSec` sets the timeout for this check in seconds. If `timeout` is not set, or it is set to `0`,
then the timeout is infinite.

If the invariant is violated, then `invariantStatus` is set to `"VIOLATED"`, and the `trace` field contains a concrete
execution that violates the invariant. This field encodes a trace in the [ITF Format][].

**Input:**

```json
{
  "method": "checkInvariant",
  "params": {
    "sessionId": "session-identifier",
    "invariantId": invariant-identifier,
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

```sh
curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"checkInvariant","params":{"sessionId":"1","invariantId":0},"id":3}'
{"jsonrpc":"2.0","id":5,"result":{"sessionId":"1","invariantStatus":"SATISFIED"}}
```

[Jetty Server]: https://jetty.org/

[Jackson]: https://github.com/FasterXML/jackson

[JSON-RPC specification]: https://www.jsonrpc.org/specification

[Igor Konnov]: https://konnov.phd

[Thomas Pani]: https://thpani.net

[ITF Format]: https://apalache-mc.org/docs/adr/015adr-trace.html