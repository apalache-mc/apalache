package at.forsyte.apalache.io.config

import at.forsyte.apalache.io.InputSource
import org.scalatest.funsuite.AnyFunSuite

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

class TestApalacheConfigJsonParser extends AnyFunSuite {
  test("loads cvc5 as an SMT solver backend") {
    val result = ApalacheConfigJsonParser.parse("""{"checker":{"smt-solver":"cvc5"}}""")

    assert(result.isSuccess)
    assert(result.requireValue().checker.smtSolver.get == SMTSolver.CVC5)
  }

  test("reports invalid option values as configuration errors") {
    val solverResult = ApalacheConfigJsonParser.parse("""{"checker":{"smt-solver":"unknown"}}""")
    val formatResult =
      ApalacheConfigJsonParser.parse("""{"source":{"kind":"string","content":"x","format":"unknown"}}""")

    assert(!solverResult.isSuccess)
    assert(solverResult.errors.contains("$.checker.smt-solver: Unexpected SMT solver backend: unknown"))
    assert(!formatResult.isSuccess)
    assert(formatResult.errors.contains("$.source.format: Unsupported source format: unknown"))
  }

  test("serializes cvc5 as a scalar value") {
    val config = ApalacheConfig(checker = CheckerPatch(smtSolver = Some(SMTSolver.CVC5)))

    assert(ApalacheConfigJsonParser.write(config).contains(""""smt-solver":"cvc5""""))
  }

  test("preserves an explicit source format when a filename cannot express it") {
    val source = InputSource.FileSource(Path.of("trace.json"), InputSource.Format.Itf)
    val config = ApalacheConfig(source = Some(source))

    val decoded = ApalacheConfigJsonParser.parse(ApalacheConfigJsonParser.write(config))
    assert(decoded.isSuccess)
    assert(decoded.requireValue().source.get.format == InputSource.Format.Itf)
  }

  test("writes source and output at the top level and rejects the old singleton sections") {
    val config = ApalacheConfig(
        source = Some(InputSource.FileSource(Path.of("Spec.tla"), InputSource.Format.Tla)),
        output = Some(Path.of("output.tla")),
    )
    val serialized = ApalacheConfigJsonParser.write(config)
    val oldInput = ApalacheConfigJsonParser.parse("""{"input":{"source":"Spec.tla"}}""")
    val oldOutput = ApalacheConfigJsonParser.parse("""{"output":{"output":"output.tla"}}""")

    assert(serialized.contains(""""source":"Spec.tla""""))
    assert(serialized.contains(""""output":"output.tla""""))
    assert(!serialized.contains(""""input""""))
    assert(!oldInput.isSuccess)
    assert(oldInput.errors.contains("$.input: Unknown configuration key."))
    assert(!oldOutput.isSuccess)
    assert(oldOutput.errors.contains("$.output: Expected a JSON string."))
  }

  test("reports invalid paths as configuration errors") {
    val escapedNull = "\\" + "u0000"
    val result = ApalacheConfigJsonParser.parse(s"""{"run-dir":"$escapedNull"}""")

    assert(!result.isSuccess)
    assert(result.errors.exists(_.contains("$.run-dir: Invalid path")))
  }

  test("writes common options at the top level and rejects the old common section") {
    val config = ApalacheConfig(common = CommonPatch(debug = Some(true)))
    val serialized = ApalacheConfigJsonParser.write(config)
    val oldSchema = ApalacheConfigJsonParser.parse("""{"common":{"debug":true}}""")

    assert(serialized.contains(""""debug":true"""))
    assert(!serialized.contains(""""common""""))
    assert(!oldSchema.isSuccess)
    assert(oldSchema.errors.contains("$.common: Unknown configuration key."))
  }

  test("rejects unknown keys in nested groups") {
    val result = ApalacheConfigJsonParser.parse("""{"checker":{"discardDisabled":false}}""")

    assert(!result.isSuccess)
    assert(result.errors.exists(_.contains("$.checker.discardDisabled: Unknown configuration key")))
  }

  test("accepts legacy aliases with a warning") {
    val result = ApalacheConfigJsonParser.parse("""{"checker":{"timeout-smt-sec":12}}""")

    assert(result.isSuccess)
    assert(result.requireValue().checker.timeoutSmtSeconds.get == 12)
    assert(result.warnings.exists(_.contains("deprecated")))
  }

  test("rejects a canonical key together with its alias") {
    val result =
      ApalacheConfigJsonParser.parse("""{"checker":{"timeout-smt":12,"timeout-smt-sec":13}}""")

    assert(!result.isSuccess)
    assert(result.errors.exists(_.contains("Do not set both")))
  }

  test("rejects HOCON, duplicate keys, and trailing documents") {
    assert(!ApalacheConfigJsonParser.parse("checker { smt-solver = cvc5 }").isSuccess)
    assert(!ApalacheConfigJsonParser.parse("""{"checker":{},"checker":{}}""").isSuccess)
    assert(!ApalacheConfigJsonParser.parse("""{} {}""").isSuccess)
  }

  test("merges tuning maps per key while replacing ordinary values") {
    val lower =
      ApalacheConfigJsonParser
        .parse(
            """{"source":"Lower.tla","output":"lower.json","checker":{"tuning":{"a":"1","shared":"low"},"smt-solver":"z3"}}""")
        .requireValue()
    val higher =
      ApalacheConfigJsonParser
        .parse("""{"source":"Higher.tla","checker":{"tuning":{"b":"2","shared":"high"},"smt-solver":"cvc5"}}""")
        .requireValue()

    val merged = higher.mergeWithLower(lower)
    assert(merged.source.get.toString == "Higher.tla")
    assert(merged.output.get.toString == "lower.json")
    assert(merged.checker.tuning.get == Map("a" -> "1", "b" -> "2", "shared" -> "high"))
    assert(merged.checker.smtSolver.get == SMTSolver.CVC5)
  }

  test("all JSON examples in the configuration manual are valid configurations") {
    val candidates = Seq(
        Path.of("docs/src/apalache/config.md"),
        Path.of("../docs/src/apalache/config.md"),
    )
    val manual = candidates.find(Files.exists(_)).getOrElse(fail("Could not locate configuration manual"))
    val text = Files.readString(manual, StandardCharsets.UTF_8)
    val examples = """(?s)```json\s*(.*?)\s*```""".r.findAllMatchIn(text).map(_.group(1)).toSeq

    assert(examples.nonEmpty)
    examples.foreach { json =>
      val result = ApalacheConfigJsonParser.parse(json)
      assert(result.isSuccess, result.errors.mkString("; "))
    }
  }
}
