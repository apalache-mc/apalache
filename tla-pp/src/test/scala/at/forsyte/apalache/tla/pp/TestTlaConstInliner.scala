package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.UntypedPredefs.untyped
import at.forsyte.apalache.tla.lir.oper.TlaArithOper.{minus, plus}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite, Matchers}


@RunWith(classOf[JUnitRunner])
class TestTlaConstInliner extends FunSuite with BeforeAndAfterEach with Matchers {
  // some expressions to play with
  private val primitiveValuedConst = NameEx("PrimitiveValuedConst")
  private val nonPrimitiveValuedConst = NameEx("NonPrimitiveValuedConst")
  private val nonConst = NameEx("x")
  private val primitiveValue = ValEx(TlaInt(42))
  // module-level constant names
  private val constants : Set[String] = Set(primitiveValuedConst.name, nonPrimitiveValuedConst.name)
  // constants mapped to primitive values
  private val constMap = Map(primitiveValuedConst.name -> primitiveValue, nonConst.name -> primitiveValue)
  // the inliner
  private var constInliner : TlaConstInliner = _

  override def beforeEach(): Unit = {
    constInliner = new TlaConstInliner(new IdleTracker(), constants)
  }
  
  test("inlines mapped NameEx constant") {
    val input = primitiveValuedConst
    val result = constInliner.replaceConstWithValue(constMap)(input)
    result shouldBe ValEx(TlaInt(42))(Untyped())
  }

  test("passes unmapped NameEx unchanged") {
    val input = nonPrimitiveValuedConst
    val result = constInliner.replaceConstWithValue(constMap)(input)
    result shouldBe input
  }

  test("passes non-CONSTANT NameEx unchanged") {
    val input = nonConst
    val result = constInliner.replaceConstWithValue(constMap)(input)
    result shouldBe input
  }

  test("inlines nested OperEx") {
    val input = OperEx(plus, nonConst, OperEx(minus, primitiveValuedConst, nonPrimitiveValuedConst))
    val result = constInliner.replaceConstWithValue(constMap)(input)
    // should replace nested `primitiveValuedConst` with `primitiveValue`
    result shouldBe OperEx(plus, nonConst, OperEx(minus, primitiveValue, nonPrimitiveValuedConst))
  }

  test("inlines LetInEx body and operator declaration") {
    val body = OperEx(plus, nonConst, OperEx(minus, primitiveValuedConst, nonPrimitiveValuedConst))
    val operDecl = TlaOperDecl("A", List.empty, OperEx(plus, primitiveValuedConst, nonPrimitiveValuedConst))
    val input = LetInEx(body, operDecl)
    val result = constInliner.replaceConstWithValue(constMap)(input)
    // should replace `primitiveValuedConst` with `primitiveValue` in body and operator declaration
    result shouldBe LetInEx(OperEx(plus, nonConst, OperEx(minus, primitiveValue, nonPrimitiveValuedConst)),
      TlaOperDecl("A", List.empty, OperEx(plus, primitiveValue, nonPrimitiveValuedConst)))
  }
}