package org.apalachemc.integration

import apalache.BuildInfo
import org.apalachemc.integration.framework.{Forked, IntegrationTestBase}

/** Exercises the CLI version command. */
class VersionCommandTest extends IntegrationTestBase {
  test("executable prints version", Forked) {
    run("version")
      .expectSuccess()
      .expectContains(BuildInfo.version)
  }
}
