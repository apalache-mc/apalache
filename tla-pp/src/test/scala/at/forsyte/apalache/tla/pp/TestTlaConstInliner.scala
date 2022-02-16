package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner
import org.scalatest.BeforeAndAfterEach
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite
import at.forsyte.apalache.tla.lir.UntypedPredefs._

@RunWith(classOf[JUnitRunner])
class TestTlaConstInliner extends AnyFunSuite with BeforeAndAfterEach with Matchers {
  // some expressions to play with
  private val primitiveValuedConst = tla.name("PrimitiveValuedConst")
  private val nonPrimitiveValuedConst = tla.name("NonPrimitiveValuedConst")
  private val nonConst = tla.name("x")
  private val primitiveValue = tla.int(42)
  private val otherPrimitiveValue = tla.int(5)
  // module-level constant names
  private val constants: Set[String] = Set(primitiveValuedConst.name, nonPrimitiveValuedConst.name)
  // constants mapped to primitive values
  private val emptyConstMap = Map[String, ValEx]()
  private val constMap = Map(
      primitiveValuedConst.name -> primitiveValue.untyped().asInstanceOf[ValEx],
      nonConst.name -> primitiveValue.untyped().asInstanceOf[ValEx],
  )
  // declare the reference to the inliner for use in each test case, initialized to the default value
  private var constInliner: TlaConstInliner = _

  override def beforeEach(): Unit = {
    // Initialize the inliner with `constants` as module-level constants and an idle tracker.
    constInliner = TlaConstInliner(new IdleTracker(), constants)
  }

  test("replaceConstWithValue inlines mapped NameEx constant") {
    val input = primitiveValuedConst
    val result = constInliner.replaceConstWithValue(constMap)(input)
    result shouldBe primitiveValue.untyped()
  }

  test("replaceConstWithValue returns unmapped NameEx unchanged") {
    val input = nonPrimitiveValuedConst
    val result = constInliner.replaceConstWithValue(constMap)(input)
    result shouldBe input.untyped()
  }

  test("replaceConstWithValue returns non-CONSTANT NameEx unchanged") {
    val input = nonConst
    val result = constInliner.replaceConstWithValue(constMap)(input)
    result shouldBe input.untyped()
  }

  test("replaceConstWithValue inlines nested OperEx") {
    val input = tla.plus(nonConst, tla.minus(primitiveValuedConst, nonPrimitiveValuedConst))
    val result = constInliner.replaceConstWithValue(constMap)(input)
    // should replace nested `primitiveValuedConst` with `primitiveValue`
    result shouldBe tla.plus(nonConst, tla.minus(primitiveValue, nonPrimitiveValuedConst)).untyped()
  }

  test("replaceConstWithValue leaves nested OperEx without primitive-valued constants unchanged") {
    val input = tla.plus(nonConst, tla.minus(nonConst, nonPrimitiveValuedConst))
    val result = constInliner.replaceConstWithValue(constMap)(input)
    result shouldBe input.untyped()
  }

  test("replaceConstWithValue inlines LetInEx body and operator declaration") {
    val body = tla.plus(nonConst, tla.minus(primitiveValuedConst, nonPrimitiveValuedConst))
    val operDecl = tla.declOp("A", tla.plus(primitiveValuedConst, nonPrimitiveValuedConst))
    val input = tla.letIn(body, operDecl.untypedOperDecl())
    val result = constInliner.replaceConstWithValue(constMap)(input)
    // should replace `primitiveValuedConst` with `primitiveValue` in body and operator declaration
    val expectedBody = tla.plus(nonConst, tla.minus(primitiveValue, nonPrimitiveValuedConst))
    val expectedOperDecl = tla.declOp("A", tla.plus(primitiveValue, nonPrimitiveValuedConst)).untypedOperDecl()
    result shouldBe tla.letIn(expectedBody, expectedOperDecl).untyped()
  }

  test("replaceConstWithValue inlines only LetInEx body if operator declaration without primitive-valued constants") {
    val body = tla.plus(nonConst, tla.minus(primitiveValuedConst, nonPrimitiveValuedConst))
    val operDecl = tla.declOp("A", tla.plus(nonConst, nonPrimitiveValuedConst))
    val input = tla.letIn(body, operDecl.untypedOperDecl())
    val result = constInliner.replaceConstWithValue(constMap)(input)
    // should replace `primitiveValuedConst` with `primitiveValue` only in body
    val expectedBody = tla.plus(nonConst, tla.minus(primitiveValue, nonPrimitiveValuedConst))
    val expectedOperDecl = operDecl.untypedOperDecl()
    result shouldBe tla.letIn(expectedBody, expectedOperDecl).untyped()
  }

  test("replaceConstWithValue inlines only LetInEx operator declaration if body without primitive-valued constants") {
    val body = tla.plus(nonConst, nonPrimitiveValuedConst)
    val operDecl = tla.declOp("A", tla.plus(primitiveValuedConst, nonPrimitiveValuedConst))
    val input = tla.letIn(body, operDecl.untypedOperDecl())
    val result = constInliner.replaceConstWithValue(constMap)(input)
    // should replace `primitiveValuedConst` with `primitiveValue` in body and operator declaration
    val expectedBody = body
    val expectedOperDecl = tla.declOp("A", tla.plus(primitiveValue, nonPrimitiveValuedConst)).untypedOperDecl()
    result shouldBe tla.letIn(expectedBody, expectedOperDecl).untyped()
  }

  test(
      "replaceConstWithValue leaves LetInEx unchanged if neither operator declaration nor body contain primitive-valued constants") {
    val body = tla.plus(nonConst, nonPrimitiveValuedConst)
    val operDecl = tla.declOp("A", tla.plus(nonConst, nonPrimitiveValuedConst))
    val input = tla.letIn(body, operDecl.untypedOperDecl())
    val result = constInliner.replaceConstWithValue(constMap)(input)
    // should replace `primitiveValuedConst` with `primitiveValue` in body and operator declaration
    val expectedBody = body
    val expectedOperDecl = operDecl.untypedOperDecl()
    result shouldBe tla.letIn(expectedBody, expectedOperDecl).untyped()
  }

  test("buildConstMap does not extract non-module constants") {
    val input = tla.eql(nonConst, primitiveValue)
    val result = constInliner.buildConstMap(emptyConstMap)(input)
    result shouldBe empty
  }

  test("buildConstMap extracts constant from equality with empty initial map") {
    val input = tla.eql(primitiveValuedConst, primitiveValue)
    val result = constInliner.buildConstMap(emptyConstMap)(input)
    result should contain only (primitiveValuedConst.name -> primitiveValue.untyped())
  }

  test("buildConstMap extracts constant from equality already present in initial map") {
    val input = tla.eql(primitiveValuedConst, primitiveValue)
    val result = constInliner.buildConstMap(constMap)(input)
    result shouldBe constMap
  }

  test("buildConstMap throws extracting constant with different value in initial map") {
    val input = tla.eql(primitiveValuedConst, otherPrimitiveValue)
    a[TlaInputError] should be thrownBy constInliner.buildConstMap(constMap)(input)
  }

  test("buildConstMap extracts constants from nested equalities") {
    val input = tla.and(tla.eql(primitiveValuedConst, primitiveValue), tla.eql(nonConst, otherPrimitiveValue))
    val result = constInliner.buildConstMap(emptyConstMap)(input)
    result should contain only (primitiveValuedConst.name -> primitiveValue.untyped())
  }

  test("buildConstMap extracts constants from LET IN expressions") {
    val body = tla.eql(primitiveValuedConst, primitiveValue)
    val operDecl = tla.declOp("A", tla.plus(nonConst, nonPrimitiveValuedConst))
    val input = tla.letIn(body, operDecl.untypedOperDecl())
    val result = constInliner.buildConstMap(emptyConstMap)(input)
    result should contain only (primitiveValuedConst.name -> primitiveValue.untyped())
  }

  test("buildConstMap doesn't extract constants from NameEx and ValEx") {
    constInliner.buildConstMap(emptyConstMap)(primitiveValuedConst) shouldBe empty
    constInliner.buildConstMap(emptyConstMap)(primitiveValue) shouldBe empty
  }
}
