package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.io.config.Constants._
import at.forsyte.apalache.io.config._
import org.scalatest.funsuite.AnyFunSuite

class TestCommandConfig extends AnyFunSuite {

  test("every command option documents its default behavior") {
    val commands = List(
        new CheckCmd(),
        new ConfigCmd(),
        new ParseCmd(),
        new ServerCmd(),
        new SimulateCmd(),
        new TestCmd(),
        new TraceeCmd(),
        new TranspileCmd(),
        new TypeCheckCmd(),
    )

    commands.foreach { command =>
      val missingDefaults = command.options
        .filterNot(_.description.exists(_.contains("default:")))
        .map(_.name)
        .toList
        .sorted

      assert(
          missingDefaults.isEmpty,
          s"${command.label}: options without documented defaults: ${missingDefaults.mkString(", ")}",
      )
    }
  }

  test("enum options document every canonical value") {
    val checker = new CheckCmd()
    assertOptionLists(checker, ALGO, Algorithm.values.map(_.name))
    assertOptionLists(checker, SMT_ENCODING, SMTEncoding.values.map(_.name))
    assertOptionLists(checker, SMT_SOLVER, SMTSolver.values.map(_.name))
    assertOptionLists(new ServerCmd(), SERVER_TYPE, ServerType.values.map(_.name))
  }

  test("CLI commands own user-facing enum descriptions") {
    val checker = new CheckCmd()
    assertOptionLists(checker, ALGO, List("remote (used by explorer)"))
    assertOptionLists(checker, SMT_ENCODING, List("arrays (experimental)", "funArrays (experimental)"))
    assertOptionLists(checker, SMT_SOLVER, List("cvc5 (experimental)"))
    assertOptionLists(new ServerCmd(), SERVER_TYPE, List("'checker' (shai-grpc)", "'explorer' (json-rpc)"))
  }

  test("specialized command patches merge over inherited command fields") {
    val command = new CheckCmd()
    command.read(List("CommandConfig.tla"))
    command.debug = Some(true)
    command.length = Some(4)
    command.algo = Some(Algorithm.Offline)

    val result = command.toConfig
    assert(result.isSuccess)
    val config = result.requireValue()
    assert(config.context.command.contains(CHECK))
    assert(config.common.debug.contains(true))
    assert(config.source.exists(_.toString == "CommandConfig.tla"))
    assert(config.checker.length.contains(4))
    assert(config.checker.algorithm.contains(Algorithm.Offline))
  }

  test("omitted checker flags do not override lower-precedence tuning") {
    val lower = ApalacheConfig(
        common = CommonPatch(debug = Some(true)),
        checker = CheckerPatch(tuning = Some(Map(
                "custom" -> "value",
                "search.seed" -> "17",
                "search.outputTraces" -> "true",
            ))),
    )
    val command = new CheckCmd()
    command.read(List("CommandConfig.tla"))

    val sparse = command.toConfig.requireValue()
    assert(sparse.checker.tuning.isEmpty)
    assert(sparse.typechecker.inferPoly.isEmpty)
    val inherited = sparse.mergeWithLower(lower)
    assert(inherited.common.debug.contains(true))
    assert(inherited.checker.tuning.flatMap(_.get("search.seed")).contains("17"))
    assert(inherited.checker.tuning.flatMap(_.get("search.outputTraces")).contains("true"))

    command.saveRuns = Some(false)
    command.seed = Some(42)
    val explicit = command.toConfig.requireValue().mergeWithLower(lower)
    assert(explicit.checker.tuning.flatMap(_.get("custom")).contains("value"))
    assert(explicit.checker.tuning.flatMap(_.get("search.seed")).contains("42"))
    assert(explicit.checker.tuning.flatMap(_.get("search.outputTraces")).contains("false"))
  }

  test("seed is validated and overrides the equivalent tuning option") {
    val invalid = new CheckCmd()
    invalid.read(List("CommandConfig.tla"))
    invalid.seed = Some(-1)
    val invalidResult = invalid.toConfig
    assert(!invalidResult.isSuccess)
    assert(invalidResult.errors.contains("Invalid --seed: expected a nonnegative integer, found -1"))

    val command = new CheckCmd()
    command.read(List("CommandConfig.tla"))
    command.tuningOptions = Some("search.seed=7")
    command.seed = Some(42)
    val config = command.toConfig.requireValue()
    assert(config.checker.tuning.flatMap(_.get("search.seed")).contains("42"))
  }

  test("server and simulation parser defaults remain lower precedence") {
    val serverCommand = new ServerCmd()
    serverCommand.read(Nil)
    val serverPatch = serverCommand.toConfig.requireValue()
    assert(serverPatch.server == ServerPatch())

    val serverConfig =
      serverPatch.mergeWithLower(ApalacheConfig(server = ServerPatch(
              port = Some(9000),
              serverType = Some(ServerType.Explorer),
          )))
    assert(serverConfig.server.port.contains(9000))
    assert(serverConfig.server.serverType.contains(ServerType.Explorer))

    val explicitServerCommand = new ServerCmd()
    explicitServerCommand.read(List("--server-type=explorer"))
    assert(explicitServerCommand.toConfig.requireValue().server.serverType.contains(ServerType.Explorer))

    val simulateCommand = new SimulateCmd()
    simulateCommand.read(List("CommandConfig.tla"))
    val simulationPatch = simulateCommand.toConfig.requireValue()
    val simulationConfig = simulationPatch.mergeWithLower(
        ApalacheConfig(checker = CheckerPatch(tuning = Some(Map("search.simulation.maxRun" -> "17")))))
    assert(simulationConfig.checker.tuning.flatMap(_.get("search.simulation")).contains("true"))
    assert(simulationConfig.checker.tuning.flatMap(_.get("search.simulation.maxRun")).contains("17"))

    simulateCommand.maxRun = Some(5)
    val explicitMaxRun = simulateCommand.toConfig.requireValue().mergeWithLower(simulationConfig)
    assert(explicitMaxRun.checker.tuning.flatMap(_.get("search.simulation.maxRun")).contains("5"))
  }

  private def assertOptionLists(command: ApalacheCommand, optionName: String, values: List[String]): Unit = {
    val description = command.options.find(_.name == optionName).flatMap(_.description).getOrElse("")
    values.foreach(value => assert(description.contains(value), s"$optionName does not document $value"))
  }
}
