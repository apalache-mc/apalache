package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

@RunWith(classOf[JUnitRunner])
class TestArithmeticBuilder extends BuilderTest {
  def testBinaryOperAndBuilderMethod(
      oper: TlaArithOper,
      method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction,
      retT: TlaType1): Unit = {

    type T = (TBuilderInstruction, TBuilderInstruction)
    type TParam = Unit

    def mkWellTyped(@unused tparam: TParam): T =
      (
          builder.name("x", IntT1),
          builder.name("y", IntT1),
      )

    def mkIllTyped(@unused tparam: TParam): Seq[T] =
      Seq(
          (
              builder.name("x", IntT1),
              builder.name("y", InvalidTypeMethods.notInt),
          ),
          (
              builder.name("x", InvalidTypeMethods.notInt),
              builder.name("y", IntT1),
          ),
      )

    def resultIsExpected = expectEqTyped[TParam, T](
        oper,
        mkWellTyped,
        ToSeq.binary,
        _ => retT,
    )

    checkRun(Generators.unitGen)(
        runBinary(
            method,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("plus") {
    testBinaryOperAndBuilderMethod(TlaArithOper.plus, builder.plus, IntT1)
  }

  test("minus") {
    testBinaryOperAndBuilderMethod(TlaArithOper.minus, builder.minus, IntT1)
  }

  test("uminus") {
    type T = TBuilderInstruction
    type TParam = Unit

    def mkWellTyped(@unused tparam: TParam): T = builder.name("x", IntT1)

    def mkIllTyped(@unused tparam: TParam): Seq[T] =
      Seq(
          builder.name("x", InvalidTypeMethods.notInt)
      )

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaArithOper.uminus,
        mkWellTyped,
        ToSeq.unary,
        _ => IntT1,
    )

    checkRun(Generators.unitGen)(
        runUnary(
            builder.uminus,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("mult") {
    testBinaryOperAndBuilderMethod(TlaArithOper.mult, builder.mult, IntT1)
  }

  test("div") {
    testBinaryOperAndBuilderMethod(TlaArithOper.div, builder.div, IntT1)
  }

  test("mod") {
    testBinaryOperAndBuilderMethod(TlaArithOper.mod, builder.mod, IntT1)
  }

  test("exp") {
    testBinaryOperAndBuilderMethod(TlaArithOper.exp, builder.exp, IntT1)
  }

  test("dotdot") {
    testBinaryOperAndBuilderMethod(TlaArithOper.dotdot, builder.dotdot, SetT1(IntT1))
  }

  test("lt") {
    testBinaryOperAndBuilderMethod(TlaArithOper.lt, builder.lt, BoolT1)
  }

  test("gt") {
    testBinaryOperAndBuilderMethod(TlaArithOper.gt, builder.gt, BoolT1)
  }

  test("le") {
    testBinaryOperAndBuilderMethod(TlaArithOper.le, builder.le, BoolT1)
  }

  test("ge") {
    testBinaryOperAndBuilderMethod(TlaArithOper.ge, builder.ge, BoolT1)
  }

}
