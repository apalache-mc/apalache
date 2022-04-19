package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfter
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestLeafBuilder extends AnyFunSuite with BeforeAndAfter {

  var varPool = new TypeVarPool()
  var sigGen = new SignatureGenerator(varPool)
  var builder = new ScopedBuilder(sigGen)

  before {
    varPool = new TypeVarPool()
    sigGen = new SignatureGenerator(varPool)
    builder = new ScopedBuilder(sigGen)
  }

  test("literals") {

    val oneW = builder.int(1)
    val oneEx: TlaEx = build(oneW)

    assert(oneEx.eqTyped(ValEx(TlaInt(1))(Typed(IntT1()))))

    val xW = builder.str("x")
    val xEx: TlaEx = build(xW)

    assert(xEx.eqTyped(ValEx(TlaStr("x"))(Typed(StrT1()))))

    val trueW = builder.bool(true)
    val trueEx: TlaEx = build(trueW)

    assert(trueEx.eqTyped(ValEx(TlaBool(true))(Typed(BoolT1()))))

  }

  test("names and scope") {

    val xInt = builder.name("x", IntT1())

    val xBool = builder.name("x", BoolT1())

    // ok separately
    val xIntEx = build(xInt)

    assert(xIntEx.eqTyped(NameEx("x")(Typed(IntT1()))))

    val xBoolEx = build(xBool)

    assert(xBoolEx.eqTyped(NameEx("x")(Typed(BoolT1()))))

    // Throw if in same scope
    assertThrows[BuilderScopeException] {
      val both = for {
        _ <- xInt
        _ <- xBool
      } yield ()
      both.run(MetaInfo(Map.empty))
    }

  }
}
