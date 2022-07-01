package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFiniteSetOper
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

@RunWith(classOf[JUnitRunner])
class TestFiniteSetBuilder extends BuilderTest {

  test("isFiniteSet") {

    type T = TBuilderInstruction

    def mkWellTyped(tt: TlaType1): T =
      builder.name("S", SetT1(tt))
    def mkIllTyped(@unused tt: TlaType1): Seq[T] =
      Seq(
          builder.name("S", InvalidTypeMethods.notSet)
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaFiniteSetOper.isFiniteSet,
        mkWellTyped,
        Seq(_),
        { _ => BoolT1 },
    )

    checkRun(
        runUnary(
            builder.isFiniteSet,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("card") {

    type T = TBuilderInstruction

    def mkWellTyped(tt: TlaType1): T =
      builder.name("S", SetT1(tt))
    def mkIllTyped(@unused tt: TlaType1): Seq[T] =
      Seq(
          builder.name("S", InvalidTypeMethods.notSet)
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaFiniteSetOper.cardinality,
        mkWellTyped,
        Seq(_),
        { _ => IntT1 },
    )

    checkRun(
        runUnary(
            builder.card,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

}
