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
    "sources": [ <rootModuleInBase64>, <importedModule1InBase64>, ... ]
  }
}
```

**Output:**

```json
{
  "result": {
    "sessionId": "<unique session identifier>"
  }
}
```

**Example**:

```sh
SPEC=`cat <<EOF | base64
---- MODULE Inc ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
=====================
EOF`
curl -X POST http://localhost:8822/rpc \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"loadSpec","params":{"sources": [ "'${SPEC}'" ]},"id":1}'
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
    "sessionId": "<session identifier>"
  }
}
```

**Output:**

On success, the server returns the identifier of the disposed session.
This identifier cannot be used in the future calls.

```json
{
  "result": {
    "sessionId": "<session identifier>"
  }
}
```

**Example**:

```sh
curl -X POST http://localhost:8822/rpc \
-H "Content-Type: application/json" \
-d '{"jsonrpc":"2.0","method":"disposeSpec","params":{"sessionId": "1a1555f8"},"id":2}'
```

[Jetty Server]: https://jetty.org/
[Jackson]: https://github.com/FasterXML/jackson
[JSON-RPC specification]: https://www.jsonrpc.org/specification
[Igor Konnov]: https://konnov.phd
[Thomas Pani]: https://thpani.net