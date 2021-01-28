package at.forsyte.apalache.io.tlc

import at.forsyte.apalache.io.tlc.config.{ConfigIntValue, ConfigModelValue, ConfigSetValue, ConfigStrValue, InitNextSpec, TemporalSpec, TlcConfigParseError}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
  * Tests for the TLC configuration parser.
  *
  * @author Igor Konnov
  */
@RunWith(classOf[JUnitRunner])
class TestTlcConfigParserApalache extends FunSuite {

  test("INIT-NEXT") {
    val text =
      """
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.behaviorSpec == InitNextSpec("Init", "Next"))
  }

  test("NEXT-INIT") {
    val text =
      """
        |NEXT Next
        |INIT Init
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.behaviorSpec == InitNextSpec("Init", "Next"))
  }

  test("Malformed INIT-NEXT") {
    val text =
      """
        |INIT
        |NEXT Next
      """.stripMargin

    assertThrows[TlcConfigParseError](TlcConfigParserApalache(text))
  }

  test("SPECIFICATION") {
    val text =
      """
        |SPECIFICATION Spec
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.behaviorSpec == TemporalSpec("Spec"))
  }

  test("CONSTANT assignments with model values") {
    val text =
      """
        |INIT Init
        |NEXT Next
        |CONSTANT
        |N = M
        |K = L
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.constAssignments == Map("N" -> ConfigModelValue("M"), "K" -> ConfigModelValue("L")))
    assert(config.constReplacements.isEmpty)
  }

  test("CONSTANT assignments with numbers") {
    val text =
      """
        |CONSTANT
        |N = 10
        |K = -20
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.constAssignments == Map("N" -> ConfigIntValue(10), "K" -> ConfigIntValue(-20)))
    assert(config.constReplacements.isEmpty)
  }

  test("CONSTANT assignments with strings") {
    val text =
      """
        |CONSTANTS
        |N = "foo"
        |K = "bar"
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.constAssignments == Map("N" -> ConfigStrValue("foo"), "K" -> ConfigStrValue("bar")))
    assert(config.constReplacements.isEmpty)
  }

  test("CONSTANT assignments with sets") {
    val text =
      """
        |CONSTANTS
        |N = {"foo", {1, Moo}}
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.constAssignments ==
      Map("N" -> ConfigSetValue(ConfigStrValue("foo"), ConfigSetValue(ConfigIntValue(1), ConfigModelValue("Moo")))))
    assert(config.constReplacements.isEmpty)
  }

  test("CONSTANT assignments and SYMMETRY") {
    val text =
      """
        |CONSTANT
        |N = M
        |\* symmetry definitions are skipped by our parser
        |SYMMETRY symmDef1
        |CONSTANT K = L
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.constAssignments == Map("N" -> ConfigModelValue("M"), "K" -> ConfigModelValue("L")))
    assert(config.constReplacements.isEmpty)
  }

  test("CONSTANT assignments and VIEW") {
    val text =
      """
        |VIEW viewDef1
        |CONSTANT
        |N = M
        |\* vire definitions are skipped by our parser
        |CONSTANT K = L
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.constAssignments == Map("N" -> ConfigModelValue("M"), "K" -> ConfigModelValue("L")))
    assert(config.constReplacements.isEmpty)
  }

  test("CONSTANT replacements") {
    val text =
      """
        |CONSTANT
        |A <- B
        |C <- D
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.constAssignments.isEmpty)
    assert(config.constReplacements == Map("A" -> "B", "C" -> "D"))
  }

  test("CONSTANT assignments and replacements") {
    val text =
      """
        |CONSTANTS
        |N = M
        |A <- B
        |K = L
        |C <- D
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.constAssignments == Map("N" -> ConfigModelValue("M"), "K" -> ConfigModelValue("L")))
    assert(config.constReplacements == Map("A" -> "B", "C" -> "D"))
  }

  test("INIT-NEXT and INVARIANTS") {
    val text =
      """
        |INIT Init
        |NEXT Next
        |INVARIANT Inv1
        |INVARIANTS Inv2
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.behaviorSpec == InitNextSpec("Init", "Next"))
    assert(config.invariants == List("Inv1", "Inv2"))
  }

// TODO: should this test succeed or fail?
//  currently it fails, because the order of TLC config sections is strictly prescribed
//
//  test("INIT-NEXT and INVARIANTS reordered") {
//    val text =
//      """
//        |INVARIANT Inv1
//        |INIT Init
//        |INVARIANTS Inv2
//        |NEXT Next
//      """.stripMargin
//
//    val config = TlcConfigParser(text)
//    assert(config.behaviorSpec == InitNextSpec("Init", "Next"))
//    assert(config.invariants == List("Inv1", "Inv2"))
//  }

  test("INIT-NEXT and PROPERTIES") {
    val text =
      """
        |INIT Init
        |NEXT Next
        |PROPERTY Prop1
        |PROPERTIES Prop2
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.behaviorSpec == InitNextSpec("Init", "Next"))
    assert(config.temporalProps == List("Prop1", "Prop2"))
  }

  test("INIT-NEXT and CONSTRAINTS") {
    val text =
      """
        |CONSTRAINTS Cons1
        |Cons2
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.behaviorSpec == InitNextSpec("Init", "Next"))
    assert(config.stateConstraints == List("Cons1", "Cons2"))
  }

  test("INIT-NEXT and ACTION_CONSTRAINTS") {
    val text =
      """
        |ACTION_CONSTRAINTS Cons1
        |Cons2
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.behaviorSpec == InitNextSpec("Init", "Next"))
    assert(config.actionConstraints == List("Cons1", "Cons2"))
  }

  test("INIT-NEXT and single-line comments") {
    val text =
      """
        |\* this is the initialization section
        |INIT Init
        |\* this the transition relation
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.behaviorSpec == InitNextSpec("Init", "Next"))
  }

  test("INIT-NEXT and multi-line comments") {
    val text =
      """
        |(*
        |  this is the initialization section
        |  *)
        |INIT Init
        |(*
        | * This is the transition predicate
        | *)
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.behaviorSpec == InitNextSpec("Init", "Next"))
  }

  test("all features") {
    val text =
      """
        |CONSTANTS
        |N = M
        |A <- B
        |CONSTRAINT
        |Cons1
        |ACTION_CONSTRAINT
        |Cons2
        |INIT Init
        |NEXT Next
        |INVARIANT
        |Inv
        |PROPERTY
        |Prop
        |ALIAS
        |Baz
        |POSTCONDITION
        |Church
        |CHECK_DEADLOCK
        |TRUE
      """.stripMargin

    val config = TlcConfigParserApalache(text)
    assert(config.constAssignments == Map("N" -> ConfigModelValue("M")))
    assert(config.constReplacements == Map("A" -> "B"))
  }
}
