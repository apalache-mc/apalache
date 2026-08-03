package org.apalachemc.integration

import org.apalachemc.integration.framework.IntegrationTestBase

/** Exercises representative CLI parse scenarios. */
class ParseCommandTest extends IntegrationTestBase {
  test("parse blank file fails nicely") {
    val blank = workspace.write("blank.tla", "")

    run("parse", outDirArgument, blank.toString)
      .expectExit(255)
      .expectOutput("""
          |...
          |Parsing error: No root module defined in file
          |...
          |EXITCODE: ERROR (255)
          |""".stripMargin)
  }

  test("parse --output=annotations.json Annotations succeeds") {
    val output = workspace.root.resolve("output.json")

    run(
        "parse",
        outDirArgument,
        s"--output=$output",
        workspace.fixture("Annotations.tla").toString,
    ).expectSuccess()
      .expectOutput("""
          |...
          |EXITCODE: OK
          |""".stripMargin)

    val json = ujson.read(workspace.read(output))
    assert(json("name").str == "ApalacheIR")
    assert(json("version").str == "1.0")
    assert(json("modules").arr.nonEmpty)
  }
}
