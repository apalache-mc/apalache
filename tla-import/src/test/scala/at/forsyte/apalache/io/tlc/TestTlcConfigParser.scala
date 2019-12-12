package at.forsyte.apalache.io.tlc

import at.forsyte.apalache.io.tlc.config.{InitNextSpec, TemporalSpec, TlcConfigParseError}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
  * Tests for the TLC configuration parser.
  *
  * @author Igor Konnov
  */
@RunWith(classOf[JUnitRunner])
class TestTlcConfigParser extends FunSuite {

  test("INIT-NEXT") {
    val text =
      """
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParser(text)
    assert(config.behaviorSpec == InitNextSpec("Init", "Next"))
  }

  test("Malformed INIT-NEXT") {
    val text =
      """
        |INIT
        |NEXT Next
      """.stripMargin

    assertThrows[TlcConfigParseError](TlcConfigParser(text))
  }

  test("SPECIFICATION") {
    val text =
      """
        |SPECIFICATION Spec
      """.stripMargin

    val config = TlcConfigParser(text)
    assert(config.behaviorSpec == TemporalSpec("Spec"))
  }

  test("CONSTANT assignments") {
    val text =
      """
        |CONSTANT
        |N = M
        |K = L
        |INIT Init
        |NEXT Next
      """.stripMargin

    val config = TlcConfigParser(text)
    assert(config.constAssignments == Map("N" -> "M", "K" -> "L"))
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

    val config = TlcConfigParser(text)
    assert(config.constAssignments == Map("N" -> "M", "K" -> "L"))
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

    val config = TlcConfigParser(text)
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

    val config = TlcConfigParser(text)
    assert(config.constAssignments == Map("N" -> "M", "K" -> "L"))
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

    val config = TlcConfigParser(text)
    assert(config.behaviorSpec == InitNextSpec("Init", "Next"))
    assert(config.invariants == List("Inv1", "Inv2"))
  }

  test("INIT-NEXT and PROPERTIES") {
    val text =
      """
        |INIT Init
        |NEXT Next
        |PROPERTY Prop1
        |PROPERTIES Prop2
      """.stripMargin

    val config = TlcConfigParser(text)
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

    val config = TlcConfigParser(text)
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

    val config = TlcConfigParser(text)
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

    val config = TlcConfigParser(text)
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

    val config = TlcConfigParser(text)
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
      """.stripMargin

    val config = TlcConfigParser(text)
    assert(config.constAssignments == Map("N" -> "M"))
    assert(config.constReplacements == Map("A" -> "B"))
  }
}
