package org.apalachemc.integration

import org.apalachemc.integration.framework.IntegrationTestBase

/** Exercises representative CLI typecheck scenarios. */
class TypecheckCommandTest extends IntegrationTestBase {
  test("typecheck can consume own --output") {
    val output = workspace.root.resolve("output.json")

    run(
        "typecheck",
        outDirArgument,
        s"--output=$output",
        workspace.fixture("Annotations.tla").toString,
    ).expectSuccess()

    val json = ujson.read(workspace.read(output))
    assert(json("name").str == "ApalacheIR")
    assert(json("modules").arr.nonEmpty)

    run("typecheck", outDirArgument, output.toString)
      .expectSuccess()
      .expectOutput("""
          |...
          |EXITCODE: OK
          |""".stripMargin)
  }

  test("typecheck Bug914 fails") {
    run("typecheck", outDirArgument, workspace.fixture("Bug914.tla").toString)
      .expectExit(120)
      .expectOutput("""
          |...
          |[Bug914.tla:21:9-21:26]: Arguments to = should have the same type. For arguments m, ["foo" ↦ TRUE] with types {  }, { foo: Bool }, in expression m = (["foo" ↦ TRUE])
          |[Bug914.tla:21:1-21:26]: Error when computing the type of Init
          |...
          |EXITCODE: ERROR (120)
          |""".stripMargin)
  }
}
