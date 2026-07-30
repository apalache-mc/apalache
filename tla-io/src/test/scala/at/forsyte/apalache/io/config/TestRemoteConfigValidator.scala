package at.forsyte.apalache.io.config

import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.io.tuning.FineTuningParser
import org.scalatest.funsuite.AnyFunSuite

class TestRemoteConfigValidator extends AnyFunSuite {
  test("accepts in-memory input and ordinary non-filesystem options") {
    val config = ApalacheConfig(
        source = Some(InputSource.StringSource("---- MODULE M ----\n====")),
        checker = CheckerPatch(
            length = Some(3),
            tuning = Some(Map("search.invariant.mode" -> "before")),
        ),
    )

    val result = RemoteConfigValidator.validate(config)

    assert(result.isSuccess)
    assert(result.requireValue() == config)
  }

  test("rejects every request-controlled filesystem field") {
    val cases = Seq(
        "$.config-file" -> """{"config-file":"config.json"}""",
        "$.out-dir" -> """{"out-dir":"out"}""",
        "$.run-dir" -> """{"run-dir":"run"}""",
        "$.output" -> """{"output":"output.tla"}""",
        "$.source" -> """{"source":"input.tla"}""",
        "$.checker.config" -> """{"checker":{"config":"M.cfg"}}""",
        "$.tracee.trace" -> """{"tracee":{"trace":"trace.itf.json"}}""",
    )

    cases.foreach { case (path, json) =>
      withClue(path) {
        val result = RemoteConfigValidator.parse(json)
        assert(!result.isSuccess)
        assert(result.errors.exists(_.startsWith(path)))
      }
    }
  }

  test("rejects every file-writing tuning key and accepts other tuning keys") {
    assert(RemoteConfigValidator.FileWritingTuningKeys.subsetOf(FineTuningParser.fieldTypes.keySet))

    RemoteConfigValidator.FileWritingTuningKeys.foreach { key =>
      withClue(key) {
        val result = RemoteConfigValidator.parse(s"""{"checker":{"tuning":{"$key":"true"}}}""")
        assert(!result.isSuccess)
        assert(result.errors.exists(_.contains(key)))
      }
    }

    val safe = RemoteConfigValidator.parse(
        """{"checker":{"tuning":{"search.invariant.mode":"before"}}}"""
    )
    assert(safe.isSuccess)
  }

  test("parse rejects a textual file source without trying to load it") {
    val result = RemoteConfigValidator.parse("""{"source":"does-not-exist.tla"}""")

    assert(!result.isSuccess)
    assert(result.errors.exists(_.startsWith("$.source")))
  }

  test("parse accepts an in-memory source object") {
    val result = RemoteConfigValidator.parse(
        """{"source":{"kind":"string","content":"---- MODULE M ----\n====","aux":[],"format":"tla"}}"""
    )

    assert(result.isSuccess)
    assert(result.requireValue().source.exists(_.isInstanceOf[InputSource.StringSource]))
  }

  test("parse rejects Quint's legacy request shape") {
    val result = RemoteConfigValidator.parse(
      """{"input":{"source":{"type":"string","content":"module M {}","format":"qnt"}},"checker":{"temporal-props":["q::temporalProps"]}}""")

    assert(!result.isSuccess)
    assert(result.errors.contains("$.input: Unknown configuration key."))
    assert(result.errors.contains("$.checker.temporal-props: Unknown configuration key."))
  }
}
