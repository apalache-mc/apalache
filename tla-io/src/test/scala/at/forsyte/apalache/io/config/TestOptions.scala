package at.forsyte.apalache.io.config

import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.io.config.Constants.{CHECK, SERVER}
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

@RunWith(classOf[JUnitRunner])
class TestOptions extends AnyFunSuite {
  test("configuration enums expose every canonical value") {
    SMTEncoding.values.foreach(value => assert(SMTEncoding.fromString(value.name) == value))
    SMTSolver.values.foreach(value => assert(SMTSolver.fromString(value.name) == value))
    Algorithm.values.foreach(value => assert(Algorithm.fromString(value.name) == value))
    SearchKind.values.foreach(value => assert(SearchKind.fromString(value.name) == value))
    ServerType.values.foreach(value => assert(ServerType.fromString(value.name) == value))
  }

  test("configuration enums reject deprecated aliases") {
    Seq("fun-arrays", "oopsla-19").foreach { alias =>
      intercept[IllegalArgumentException](SMTEncoding.fromString(alias))
    }
  }

  test("command initialization exposes command, common options, and source directly") {
    val source = InputSource.StringSource("---- MODULE M ----\n====")
    val result = ApalacheConfigResolver.resolveCommandInitialization(ApalacheConfig(
            context = RunContextPatch(command = Some(CHECK)),
            source = Some(source),
        ))

    assert(result.isSuccess)
    val initialization = result.requireValue()
    assert(initialization.command == CHECK)
    assert(initialization.source.contains(source))
    assert(!initialization.common.debug)
  }

  test("FileSource recognizes ITF files") {
    val result = InputSource.FileSource(Path.of("foo.itf.json"))
    assert(result.isSuccess)
    assert(result.requireValue().format == InputSource.Format.Itf)
  }

  test("ordinary JSON files are not recognized as ITF") {
    val result = InputSource.FileSource(Path.of("foo.json"))
    assert(result.isSuccess)
    assert(result.requireValue().format == InputSource.Format.Json)
  }

  test("resolvers use the static defaults from ApalacheConfig") {
    val defaults = ApalacheConfig.defaults
    assert(ApalacheConfig.empty.mergeWithDefaults == defaults)
    val config = ApalacheConfig(
        context = RunContextPatch(command = Some(CHECK)),
        source = Some(InputSource.StringSource("---- MODULE M ----\n====")),
    )

    val result = ApalacheConfigResolver.resolveCheck(config)
    assert(result.isSuccess)
    val options = result.requireValue()

    assert(options.common.debug == defaults.common.debug.get)
    assert(options.common.features == defaults.common.features.get)
    assert(options.common.outDir == defaults.common.outDir.get)
    assert(options.common.profiling == defaults.common.profiling.get)
    assert(options.common.smtprof == defaults.common.smtprof.get)
    assert(options.common.writeIntermediate == defaults.common.writeIntermediate.get)
    assert(options.typechecker.inferPoly == defaults.typechecker.inferPoly.get)
    assert(options.checker.algorithm == defaults.checker.algorithm.get)
    assert(options.checker.discardDisabled == defaults.checker.discardDisabled.get)
    assert(options.checker.length == defaults.checker.length.get)
    assert(options.checker.maxError == defaults.checker.maxError.get)
    assert(options.checker.timeoutSmtSeconds == defaults.checker.timeoutSmtSeconds.get)
    assert(options.checker.checkDeadlocks)
    assert(options.checker.smtSolver == defaults.checker.smtSolver.get)
    assert(options.checker.smtEncoding == defaults.checker.smtEncoding.get)
    assert(options.checker.tuning == defaults.checker.tuning.get)
    assert(options.checker.seed >= 0)
    assert(options.checker.searchKind == defaults.checker.searchKind.get)
    assert(defaults.checker.maxRun.isEmpty)
    assert(options.checker.maxRun == 1)
    assert(options.checker.outputTraces == defaults.checker.outputTraces.get)

    val serverResult = ApalacheConfigResolver.resolveServer(config.withCommand(SERVER))
    assert(serverResult.isSuccess)
    val server = serverResult.requireValue().server
    assert(server.port == defaults.server.port.get)
    assert(server.serverType == defaults.server.serverType.get)
  }

  test("sources report availability and read UTF-8 content") {
    val inMemory = InputSource.StringSource("α")
    assert(inMemory.exists)
    assert(inMemory.readUtf8.requireValue() == "α")

    val path = Files.createTempFile("apalache-source", ".tla")
    try {
      Files.writeString(path, "β", StandardCharsets.UTF_8)
      val file = InputSource.FileSource(path).requireValue()
      assert(file.exists)
      assert(file.readUtf8.requireValue() == "β")

      Files.delete(path)
      assert(!file.exists)
      assert(file.readUtf8.errors.exists(_.contains("File not found")))
    } finally {
      Files.deleteIfExists(path)
    }
  }

  test("CVC5 currently supports only the OOPSLA19 SMT encoding") {
    Seq(SMTEncoding.OOPSLA19, SMTEncoding.Arrays, SMTEncoding.FunArrays).foreach { encoding =>
      val result = ApalacheConfigResolver.resolveCheck(checkConfig(SMTSolver.Z3, encoding))
      assert(result.isSuccess)
    }

    assert(ApalacheConfigResolver.resolveCheck(checkConfig(SMTSolver.CVC5, SMTEncoding.OOPSLA19)).isSuccess)

    val invalid = ApalacheConfigResolver.resolveCheck(checkConfig(SMTSolver.CVC5, SMTEncoding.Arrays))
    assert(!invalid.isSuccess)
    val message = invalid.errors.head
    assert(message.contains("checker.smt-solver=cvc5"))
    assert(message.contains("checker.smt-encoding=oopsla19"))
    assert(message.contains("arrays"))
  }

  test("checker search controls are resolved and validated") {
    val configured = checkConfig(SMTSolver.Z3, SMTEncoding.OOPSLA19).copy(checker = CheckerPatch(
        seed = Some(42),
        searchKind = Some(SearchKind.Simulate),
        maxRun = Some(7),
        outputTraces = Some(true),
    ))
    val resolved = ApalacheConfigResolver.resolveCheck(configured)
    assert(resolved.isSuccess)
    assert(resolved.requireValue().checker.seed == 42)
    assert(resolved.requireValue().checker.searchKind == SearchKind.Simulate)
    assert(resolved.requireValue().checker.maxRun == 7)
    assert(resolved.requireValue().checker.outputTraces)

    val defaultSimulation =
      ApalacheConfigResolver.resolveCheck(checkConfig(SMTSolver.Z3, SMTEncoding.OOPSLA19).copy(
              checker = CheckerPatch(searchKind = Some(SearchKind.Simulate))))
    assert(defaultSimulation.isSuccess)
    assert(defaultSimulation.requireValue().checker.maxRun == ApalacheConfigResolver.defaultSimulationRuns)

    val explicitSingleCheck =
      ApalacheConfigResolver.resolveCheck(checkConfig(SMTSolver.Z3, SMTEncoding.OOPSLA19).copy(
              checker = CheckerPatch(searchKind = Some(SearchKind.Check), maxRun = Some(1))))
    assert(explicitSingleCheck.isSuccess)

    Seq(
        CheckerPatch(seed = Some(-1)) -> "checker.seed must be between 0 and 2147483647",
        CheckerPatch(maxRun = Some(0)) -> "checker.max-run must be positive",
        CheckerPatch(maxRun = Some(-1)) -> "checker.max-run must be positive",
        CheckerPatch(searchKind = Some(SearchKind.Check), maxRun = Some(2)) ->
          "checker.max-run must equal 1 when checker.search-kind=check",
    ).foreach { case (patch, expected) =>
      val result =
        ApalacheConfigResolver.resolveCheck(checkConfig(SMTSolver.Z3, SMTEncoding.OOPSLA19).copy(checker = patch))
      assert(!result.isSuccess)
      assert(result.errors.exists(_.contains(expected)))
    }
  }

  test("checker seed accepts Int.MaxValue during resolution") {
    val upperBound =
      ApalacheConfigResolver.resolveCheck(checkConfig(SMTSolver.Z3, SMTEncoding.OOPSLA19).copy(
              checker = CheckerPatch(seed = Some(Int.MaxValue))))
    assert(upperBound.isSuccess)
    assert(upperBound.requireValue().checker.seed == Int.MaxValue)
  }

  test("TLC deadlock settings are resolved once, with application config taking precedence") {
    val tlc = Files.createTempFile("apalache-options", ".cfg")
    try {
      Files.writeString(
          tlc,
          "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
          StandardCharsets.UTF_8,
      )
      val fromTlc = ApalacheConfigResolver.resolveCheck(checkConfig(SMTSolver.Z3, SMTEncoding.OOPSLA19).copy(
              checker = CheckerPatch(tlcConfig = Some(tlc))))
      assert(fromTlc.isSuccess)
      assert(!fromTlc.requireValue().checker.checkDeadlocks)

      val overridden =
        ApalacheConfigResolver.resolveCheck(checkConfig(SMTSolver.Z3, SMTEncoding.OOPSLA19).copy(checker = CheckerPatch(
                tlcConfig = Some(tlc),
                checkDeadlocks = Some(true),
            )))
      assert(overridden.isSuccess)
      assert(overridden.requireValue().checker.checkDeadlocks)
      assert(overridden.warnings.nonEmpty)
    } finally {
      Files.deleteIfExists(tlc)
    }
  }

  private def checkConfig(solver: SMTSolver, encoding: SMTEncoding): ApalacheConfig =
    ApalacheConfig(
        context = RunContextPatch(command = Some(CHECK)),
        source = Some(InputSource.StringSource("---- MODULE M ----\n====")),
        checker = CheckerPatch(
            smtSolver = Some(solver),
            smtEncoding = Some(encoding),
        ),
    )
}
