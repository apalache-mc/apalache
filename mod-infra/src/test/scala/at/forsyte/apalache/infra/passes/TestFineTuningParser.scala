package at.forsyte.apalache.infra.passes

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestFineTuningParser extends AnyFunSuite{
  test("can parse empty tuning options") {
    val config: Either[String, Map[String, Object]] = FineTuningParser.fromStrings(Map[String, String]())
    assert(config.isRight && config.map(_.isEmpty).contains(true))
  }

  test("parses rewriter.shortCircuit") {
    val config = FineTuningParser.fromStrings(Map("rewriter.shortCircuit" -> "true"))
    assert(config.isRight && config.exists(_.get("rewriter.shortCircuit").contains(true)))
  }

  test("fails on wrong rewriter.shortCircuit") {
    val r = "12333"
    val config = FineTuningParser.fromStrings(Map("rewriter.shortCircuit" -> r))
    assert(config.isLeft)
  }

  test("parses search.transitionFilter") {
    val r = "(0->0|1->5|2->(2|3)|[3-9]->.*|[1-9][0-9]+->.*)"
    val config =
      FineTuningParser.fromStrings(Map("search.transitionFilter" -> r))
    assert(config.isRight && config.exists(_.get("search.transitionFilter").contains(r)))
  }

  test("fails on wrong search.transitionFilter") {
    val r = "(aaaa"
    val config =
      FineTuningParser.fromStrings(Map("search.transitionFilter" -> r))
    assert(config.isLeft)
  }

  test("parses search.invariantFilter") {
    val r = "(0->0|1->5|2->(2|3)|[3-9]->.*|[1-9][0-9]+->.*)"
    val config =
      FineTuningParser.fromStrings(Map("search.invariantFilter" -> r))
    assert(config.isRight && config.exists(_.get("search.invariantFilter").contains(r)))
  }

  test("fails on wrong search.invariantFilter") {
    val r = "(aaaa"
    val config =
      FineTuningParser.fromStrings(Map("search.invariantFilter" -> r))
    assert(config.isLeft)
  }

  test("parses z3.memory_high_watermark_mb") {
    val config = FineTuningParser.fromStrings(Map("z3.memory_high_watermark_mb" -> "123"))
    assert(config.isRight && config.exists(_.get("z3.memory_high_watermark_mb").contains(123)))
  }

  test("fails on wrong z3.memory_high_watermark_mb") {
    val config = FineTuningParser.fromStrings(Map("z3.memory_high_watermark_mb" -> "aaaa"))
    assert(config.isLeft)
  }

  test("parses z3.sat.cardinality.encoding") {
    val config = FineTuningParser.fromStrings(Map("z3.sat.cardinality.encoding" -> "circuit"))
    assert(config.isRight && config.exists(_.get("z3.sat.cardinality.encoding").contains("circuit")))
  }

  test("fails on wrong z3.sat.cardinality.encoding") {
    val config = FineTuningParser.fromStrings(Map("z3.sat.cardinality.encoding" -> "aaaa"))
    assert(config.isLeft)
  }
}
