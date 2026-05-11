# ADR-025: CVC5 solver backend integration

| authors                                | last revised    |
| -------------------------------------- | --------------: |
| Thomas Pani                            | 2026-05-11      |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)
- [References](#references)

## Summary

We will add CVC5 as a native solver backend by implementing a `Cvc5SolverContext` behind Apalache's
existing `SolverContext` interface. Z3 remains the default solver while CVC5 is introduced as an opt-in
backend and validated against the current SMT encodings.

We will not use `tools.aqua:cvc5-turnkey`, because it lags current CVC5 releases. We will also not introduce
JavaSMT or KSMT for the first integration. Those abstractions remain possible future options, but the initial
CVC5 backend should preserve direct access to CVC5 options, model APIs, statistics, and solver-specific behavior.

## Context

Apalache currently exposes a solver-independent `SolverContext` interface, but the only production implementation is
`Z3SolverContext`. That class has multiple responsibilities. In addition to calling Z3, it contains backend-specific
code for several parts of the SMT integration, including:

1. Translating simplified TLA+ expressions into solver terms.
2. Constructing sorts for the OOPSLA19, Arrays, and FunArrays encodings.
3. Maintaining solver-term caches across push/pop levels.
4. Evaluating ground expressions in a model.
5. Handling debug SMT logging, metrics, timeouts, statistics, and solver-specific tuning parameters.

This means that adding cvc5 is primarily a solver-context implementation problem, not only a dependency problem.
An integration layer must preserve the existing incremental checking behavior, arena/cell naming conventions, model
decoding expectations, SMT profiling, and timeout semantics.

The packaging situation has changed since early cvc5 Java integrations.
`tools.aqua:cvc5-turnkey` exists, but it is stale relative to cvc5 releases and
should not be the dependency that gates Apalache's cvc5 support. Therefore,
Apalache should treat the official `io.github.cvc5:cvc5` artifact as the preferred native dependency
path.

## Options

1. Implement `Cvc5SolverContext` directly against the cvc5 Java API.

   This mirrors the existing architecture: keep Apalache's `SolverContext` as the internal abstraction and add another
   concrete backend next to `Z3SolverContext`. The cvc5 Java API exposes a `Solver` entry point, Java classes for
   `Sort`, `Term`, `Kind`, `Result`, and related concepts, plus model value and assertion-stack operations that map
   naturally to the current context responsibilities.

   This option keeps access to cvc5-specific options, model APIs, statistics, and future proof or unsat-core features.
   It also lets us reproduce the Z3 context's cache discipline and logging exactly where Apalache needs it. The cost is
   that term construction, sort construction, timeout handling, and model decoding will be duplicated in another
   backend-specific implementation.

2. Use JavaSMT as the common solver integration layer.

   JavaSMT provides a solver-independent `SolverContext`, formula managers for arrays, integers, Booleans, UFs, and
   other theories, plus prover environments with assertion stacks. It also has a published cvc5 solver artifact.
   JavaSMT is the more mature solver-abstraction candidate by public project signals: as of 2026-05-11, its GitHub
   mirror has 236 stars, 56 forks, 6,362 commits, 83 open issues, and 28 open pull requests. It also has publications
   from 2016 and 2021, and GitHub lists JavaSMT 6.0.0 as the latest release in 2026.

   This option is attractive if the goal is to make Z3, cvc5, and future solvers share one formula construction layer.
   However, it is a larger architectural migration than adding cvc5. Apalache would have to move the current
   `Z3SolverContext` expression construction onto JavaSMT's formula managers or introduce a second internal expression
   representation. We would also depend on JavaSMT's common-denominator API for solver options, timeout behavior,
   unsupported operations, statistics, model extraction, and exact SMT-LIB serialization. That abstraction may hide
   details that are useful while validating cvc5 against Z3 on Apalache's encodings.

3. Use KSMT as the common solver integration layer.

   KSMT provides a solver-agnostic expression representation, Java/Kotlin APIs, cvc5 support, native delivery for common
   operating systems, and support for the theories Apalache uses: arrays, uninterpreted functions, and arithmetic. It
   also advertises portfolio solving and running solvers in separate processes, which is relevant for timeout and native
   solver crash isolation. KSMT is less mature by public project signals: as of 2026-05-11, its GitHub repository has 38
   stars, 16 forks, 135 commits, 4 open issues, and 8 open pull requests. GitHub lists `0.6.4` as the latest release in
   2025.

   This option is worth revisiting if Apalache wants a broader solver abstraction later, especially if solver delivery or
   process isolation becomes more important than direct solver API access. For the first cvc5 backend, it is still a
   larger dependency and architectural shift than needed, and it would require validating all model-decoding and
   incremental-solving semantics used by Apalache.

4. Emit SMT-LIB and invoke a cvc5 process.

   This avoids JNI packaging and Java binding concerns. It could reuse `RecordingSolverContext`-style SMT-LIB output and
   call an external `cvc5` binary.

   This is useful as an oracle, debugging mode, or CI comparison target, but it is not a good first production backend
   for Apalache's current incremental checker. Maintaining interactive push/pop, timeout, model-value queries, and arena
   decoding through a process protocol would add its own adapter complexity while giving up native API type safety.

5. Use `tools.aqua:cvc5-turnkey`.

   This would resemble the current `tools.aqua:z3-turnkey` dependency style. It is not acceptable as the main path
   because the published cvc5-turnkey artifact lags current cvc5 releases.

## Solution

Implement cvc5 support as a native backend. This means adding a `Cvc5SolverContext` that implements Apalache's
existing `SolverContext` interface, keeping Z3 as the default solver, and exposing cvc5 as an opt-in backend until
parity and performance are established.

Use the official cvc5 Java API through `io.github.cvc5:cvc5` when the artifact is available for Apalache's supported
platforms. Do not use `tools.aqua:cvc5-turnkey` for the production integration. Do not introduce JavaSMT or KSMT in
the first integration.

The initial implementation should be intentionally conservative:

1. Prioritize the OOPSLA19 encoding, since it is the primary encoding used by Apalache. Arrays and FunArrays should be
   included in the compatibility work, but they are not the only target.
2. Preserve the current cell/sort naming conventions so that existing logging, recording, and model-decoding assumptions
   remain easy to compare against Z3.
3. Add a solver choice to configuration separately from `smtEncoding`; those are independent dimensions.
4. Keep backend-neutral SMT controls separate from solver-specific options. For example, `smt.randomSeed`,
   `smt.statsSec`, and SMT timeouts are concepts Apalache can define once and map to each backend. Low-level solver
   parameters should remain namespaced, for example `z3.*` and `cvc5.*`.
5. Build a cross-solver test matrix that runs all existing model-checker and rewriter tests against both Z3 and cvc5.
6. Use SMT-LIB dumps as a comparison aid.

## Consequences

This decision keeps the first cvc5 integration close to the existing code and reduces the amount of architecture that
must change before we can compare solver behavior. It also preserves access to cvc5-specific options and model APIs,
which is important while diagnosing differences from Z3.

The main downside is duplicated backend code. `Cvc5SolverContext` will likely share a large shape with
`Z3SolverContext`, and some duplication is acceptable during the first integration. After parity is established, we
should extract only the pieces that are demonstrably solver-independent, for example cell-cache lifetime, arena
consistency checks, metrics accounting, and solver-selection plumbing. This will likely need a larger refactoring.

JavaSMT and KSMT remain viable future options. The native cvc5 backend should give us evidence for whether adopting a
solver-agnostic formula layer would simplify Apalache or merely move backend-specific behavior into escape hatches.

The implementation will require dependency and CI work. cvc5 ships native code behind the Java API, so CI must verify
Linux and macOS support explicitly and document any unsupported platform combinations. If official Maven artifacts lag significantly behind a
new cvc5 release, Apalache should prefer staying on the latest compatible official artifact over depending on stale packaging.

## References

1. cvc5 repository and releases: <https://github.com/cvc5/cvc5>
2. cvc5 Java API documentation: <https://cvc5.github.io/docs/cvc5-1.2.0/api/java/java.html>
3. cvc5 Java `Solver` API documentation: <https://cvc5.github.io/docs/cvc5-1.1.0/api/java/io/github/cvc5/Solver.html>
4. Official cvc5 Maven artifact index: <https://mvnrepository.com/artifact/io.github.cvc5/cvc5>
5. cvc5-turnkey Maven index: <https://repo1.maven.org/maven2/tools/aqua/cvc5-turnkey/>
6. JavaSMT `SolverContext` API: <https://sosy-lab.github.io/java-smt/api/org/sosy_lab/java_smt/api/SolverContext.html>
7. JavaSMT `FormulaManager` API: <https://sosy-lab.github.io/java-smt/api/org/sosy_lab/java_smt/api/FormulaManager.html>
8. JavaSMT cvc5 solver artifact: <https://central.sonatype.com/artifact/org.sosy-lab/javasmt-solver-cvc5>
9. JavaSMT GitHub repository and releases: <https://github.com/sosy-lab/java-smt>
10. KSMT overview and solver/theory support: <https://ksmt.io/>
11. KSMT GitHub repository and releases: <https://github.com/UnitTestBot/ksmt>
