package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaOper}
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestHybrid extends BuilderTest {
  test("primeEq") {
    type T = (TBuilderInstruction, TBuilderInstruction)
    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("x", tt),
          builder.name("y", tt),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("x", InvalidTypeMethods.differentFrom(tt)),
              builder.name("y", tt),
          ),
          (
              builder.name("x", tt),
              builder.name("y", InvalidTypeMethods.differentFrom(tt)),
          ),
      )

    def resultIsExpected: TlaType1 => TBuilderResult => Boolean = {
      tt =>
        { resEx =>
          val (x, y) = mkWellTyped(tt)
          resEx.eqTyped(
              OperEx(
                  TlaOper.eq,
                  OperEx(TlaActionOper.prime, x)(Typed(tt)),
                  y,
              )(Typed(BoolT1()))
          )
        }
    }

    checkRun(
        runBinary(
            builder.primeEq,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

}
