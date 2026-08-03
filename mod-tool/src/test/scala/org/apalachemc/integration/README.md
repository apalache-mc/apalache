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

Tests run Tool in-process by default. Force a particular test to use a fresh JVM with `Forked`:

```scala
import org.apalachemc.integration.framework.Forked

test("exercise process isolation", Forked) {
  run("version").expectSuccess()
}
```

Run the suites with:

```sh
sbt tool/cliIntegrationTest
APALACHE_CLI_TEST_MODE=forked sbt tool/cliIntegrationTest
sbt 'tool/CliIntegration/testOnly org.apalachemc.integration.ParseCommandTest -- -z "empty module"'
```

Set `APALACHE_CLI_TEST_TIMING=true` to print the elapsed time of each Tool invocation. Suite-level
parallel execution is currently disabled because in-process runs temporarily replace JVM-global state.
