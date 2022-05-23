package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

@RunWith(classOf[JUnitRunner])
class TestFunBuilder extends BuilderTest {

  test("tuple") {
    type T = Seq[TBuilderInstruction]

    type TParam = Seq[TlaType1]

    implicit val typeSeqGen: Gen[TParam] = for {
      n <- Gen.choose(0, 5)
      seq <- Gen.listOfN(n, singleTypeGen)
    } yield seq

    def mkWellTyped(tparam: TParam): T =
      tparam.zipWithIndex.map { case (tt, i) =>
        builder.name(s"t$i", tt)
      }

    def mkIllTyped(tparam: TParam): Seq[T] = Seq.empty

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaFunOper.tuple,
        mkWellTyped,
        liftBuildToSeq,
        ts => TupT1(ts: _*),
    )

    checkRun(
        runVariadic(
            builder.tuple,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("funDef") {
    type T = (TBuilderInstruction, TBuilderInstruction, TBuilderInstruction)

    type TParam = Seq[TlaType1]

    implicit val typeSeqGen: Gen[TParam] = for {
      n <- Gen.choose(0, 5)
      seq <- Gen.listOfN(n, singleTypeGen)
    } yield seq

    def mkWellTyped(tparam: TParam): T =
      tparam.zipWithIndex.map { case (tt, i) =>
        builder.name(s"t$i", tt)
      }

    def mkIllTyped(tparam: TParam): Seq[T] = Seq.empty

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaFunOper.tuple,
        mkWellTyped,
        liftBuildToSeq,
        ts => TupT1(ts: _*),
    )

    checkRun(
        runVariadic(
            builder.tuple,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }
}
