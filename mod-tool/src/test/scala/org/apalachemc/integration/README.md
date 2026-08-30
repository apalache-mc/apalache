# CLI integration tests

Put command tests in `org.apalachemc.integration`, with one suite per CLI command. Extend
`IntegrationTestBase` to receive an isolated temporary workspace and the configured Tool runner.

```scala
package org.apalachemc.integration

import org.apalachemc.integration.framework.IntegrationTestBase

class ParseCommandTest extends IntegrationTestBase {
  private def parse(arguments: String*) = runWithOutDir("parse", arguments: _*)

  test("parse an empty module") {
    val input = workspace.write("Empty.tla", "---- MODULE Empty ----\n====\n")

    parse(input.toString)
      .expectSuccess()
      .expectContains("EXITCODE: OK")
  }
}
```

Use `workspace.write` for test-local input and `workspace.filename("Spec.tla")` for files under
`test/tla`. Tool output goes below `workspace.outDir`; the workspace is deleted after each test.

`CommandResult` provides `expectSuccess`, `expectExit`, `expectContains`, `expectNotContains`, and
`expectOutput`. Assertions inspect stdout by default; pass `isStderr = true` to inspect stderr.
`expectOutput` supports a whole-line `...` wildcard matching any number of lines.

## Configuration matrix

Suites use the configuration-independent `GENERAL` worker by default. This is appropriate for commands such as
`parse`, `typecheck`, and `version` that do not use an SMT solver. Checker suites declare the exact configurations
under which all of their tests are valid:

```scala
import org.apalachemc.integration.framework.IntegrationTestConfiguration.{ARRAYS_Z3, OOPSLA19_CVC5, OOPSLA19_Z3}
import org.apalachemc.integration.framework.IntegrationTestConfiguration

class CheckCommandTest extends IntegrationTestBase {
  override protected val supportedConfigurations: Set[IntegrationTestConfiguration] =
    Set(OOPSLA19_Z3, OOPSLA19_CVC5, ARRAYS_Z3)
}
```

The available configuration IDs are:

- `general`
- `oopsla19-z3`
- `oopsla19-cvc5`
- `arrays-z3`

`arrays-cvc5` is not supported. Put scenarios that work with every checker configuration in a shared suite. Put
OOPSLA19-only scenarios in a suite supporting `OOPSLA19_Z3` and `OOPSLA19_CVC5`, and solver-specific scenarios in a
suite supporting one configuration. Compatibility is a suite property; tags remain available for independent
categories such as temporal tests.

Each selected configuration runs in its own forked JVM. Configuration workers run in parallel, while the tests in
one worker run sequentially. The checker workers set `SMT_SOLVER` and `SMT_ENCODING` for both in-process commands
and commands that use a fresh JVM.

## Execution mode

Tests run Tool in-process by default. Force a particular test to use a fresh JVM with `Forked`:

```scala
import org.apalachemc.integration.framework.Forked

test("exercise process isolation", Forked) {
  run("version").expectSuccess()
}
```

Run the suites with:

```sh
make scala-integration
APALACHE_CLI_TEST_CONFIGS=oopsla19-cvc5 sbt tool/cliIntegrationTest
APALACHE_CLI_TEST_CONFIGS=oopsla19-z3,arrays-z3 sbt tool/cliIntegrationTest
APALACHE_CLI_TEST_MODE=forked sbt tool/cliIntegrationTest
sbt 'tool/CliIntegration/testOnly org.apalachemc.integration.ParseCommandTest -- -z "empty module"'
```

`APALACHE_CLI_TEST_CONFIGS` filters the worker IDs; if omitted, all four workers run. A `testOnly` selection is still
expanded across the selected workers, and the suite itself skips workers it does not support.

Set `APALACHE_CLI_TEST_TIMING=true` to print the active configuration and elapsed time of each Tool invocation.

ScalaTest also writes per-test start and completion events to configuration-specific JSONL files. By default they
are under `target/cli-integration-timings`; set `APALACHE_CLI_TEST_TIMING_DIR` to choose another
directory. Generate the same Markdown summary and CSV diagnostics used in GitHub Actions with:

```sh
python3 script/cli_integration_timing_report.py \
  --input target/cli-integration-timings \
  --markdown /tmp/cli-integration-timings.md \
  --csv /tmp/cli-integration-timings.csv \
  --label local
```

The Actions job summary shows quartiles, the median, Tukey outliers, and a Mermaid chart of the ten slowest tests
for each configuration. Timing data is informational and does not introduce a performance gate.
