package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfter
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
/**
 * @author
 *   Jure Kukovec
 */
class TestArithmeticBuilder extends AnyFunSuite with BeforeAndAfter {
  var varPool = new TypeVarPool()
  var sigGen = new SignatureGenerator(varPool)
  var builder = new TypeCalculatingBuilder(sigGen)

  before {
    varPool = new TypeVarPool()
    sigGen = new SignatureGenerator(varPool)
    builder = new TypeCalculatingBuilder(sigGen)
  }

  def testbinaryOperAndBuilderMethod(oper: TlaArithOper, method: (TlaEx, TlaEx) => TlaEx, retT: TlaType1) {
    val cmp = sigGen.computationFromSignatureForFixedArity(oper)

    val args = Seq(
        TlaInt(1),
        TlaInt(1),
    ).map {
      ValEx(_)(Typed(IntT1()))
    }

    val res = cmp(args)

    assert(res.contains(retT))

    val Seq(x, y) = args
    val resEx = method(x, y)

    assert(resEx.eqTyped(OperEx(oper, x, y)(Typed(retT))))

    val utArgs = Seq(
        TlaInt(1),
        TlaInt(1),
    ).map {
      ValEx(_)(Untyped())
    }

    val Seq(xUt, yUt) = utArgs

    assertThrows[TypingException] {
      method(xUt, yUt)
    }

    val badY = ValEx(TlaStr("a"))(Typed(StrT1()))

    assertThrows[TypedBuilderException] {
      method(x, badY)
    }
  }

  test("plus") {
    testbinaryOperAndBuilderMethod(TlaArithOper.plus, builder.plus, IntT1())
  }

  test("minus") {
    testbinaryOperAndBuilderMethod(TlaArithOper.minus, builder.minus, IntT1())
  }

  test("uminus") {
    val cmp = sigGen.computationFromSignatureForFixedArity(TlaArithOper.uminus)

    val x = ValEx(TlaInt(1))(Typed(IntT1()))

    val res = cmp(Seq(x))

    assert(res.contains(IntT1()))

    val resEx = builder.uminus(x)

    assert(resEx.eqTyped(OperEx(TlaArithOper.uminus, x)(Typed(IntT1()))))

    val xUt = ValEx(TlaInt(1))(Untyped())

    assertThrows[TypingException] {
      builder.uminus(xUt)
    }

    val badX = ValEx(TlaStr("a"))(Typed(StrT1()))

    assertThrows[TypedBuilderException] {
      builder.uminus(badX)
    }
  }

  test("mult") {
    testbinaryOperAndBuilderMethod(TlaArithOper.mult, builder.mult, IntT1())
  }

  test("div") {
    testbinaryOperAndBuilderMethod(TlaArithOper.div, builder.div, IntT1())
  }

  test("mod") {
    testbinaryOperAndBuilderMethod(TlaArithOper.mod, builder.mod, IntT1())
  }

  test("exp") {
    testbinaryOperAndBuilderMethod(TlaArithOper.exp, builder.exp, IntT1())
  }

  test("dotdot") {
    testbinaryOperAndBuilderMethod(TlaArithOper.dotdot, builder.dotdot, SetT1(IntT1()))
  }

  test("lt") {
    testbinaryOperAndBuilderMethod(TlaArithOper.lt, builder.lt, BoolT1())
  }

  test("gt") {
    testbinaryOperAndBuilderMethod(TlaArithOper.gt, builder.gt, BoolT1())
  }

  test("le") {
    testbinaryOperAndBuilderMethod(TlaArithOper.le, builder.le, BoolT1())
  }

  test("ge") {
    testbinaryOperAndBuilderMethod(TlaArithOper.ge, builder.ge, BoolT1())
  }

}
