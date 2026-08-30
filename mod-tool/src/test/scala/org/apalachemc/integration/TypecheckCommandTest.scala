package org.apalachemc.integration

import org.apalachemc.integration.framework.IntegrationTestBase

/** Exercises representative CLI typecheck scenarios. */
class TypecheckCommandTest extends IntegrationTestBase {
  private def typecheck(arguments: String*) = runWithOutDir("typecheck", arguments: _*)

  test("typecheck can consume own --output") {
    val output = workspace.root.resolve("output.json")

    typecheck(
        s"--output=$output",
        workspace.filename("Annotations.tla"),
    ).expectSuccess()

    val json = ujson.read(workspace.read(output))
    assert(json("name").str == "ApalacheIR")
    assert(json("modules").arr.nonEmpty)

    typecheck(output.toString)
      .expectSuccess()
      .expectOutput("""
          |...
          |EXITCODE: OK
          |""".stripMargin)
  }

  test("typecheck Bug914 fails") {
    typecheck(workspace.filename("Bug914.tla"))
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
