package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

@RunWith(classOf[JUnitRunner])
class TestBaseBuilder extends BuilderTest {

  test("eq/neq") {
    type T = (TBuilderInstruction, TBuilderInstruction)
    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("lhs", tt),
          builder.name("rhs", tt),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("lhs", InvalidTypeMethods.differentFrom(tt)),
              builder.name("rhs", tt),
          ),
          (
              builder.name("lhs", tt),
              builder.name("rhs", InvalidTypeMethods.differentFrom(tt)),
          ),
      )

    def resultIsExpected(op: TlaOper) = expectEqTyped[TlaType1, T](
        op,
        mkWellTyped,
        { case (a, b) => Seq(a, b) },
        _ => BoolT1,
    )

    def run(
        op: TlaOper,
        method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction,
      )(tt: TlaType1): Boolean =
      runBinary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(op),
      )(tt)

    checkRun(run(TlaOper.eq, builder.eql))
    checkRun(run(TlaOper.ne, builder.neql))
  }

  test("appOp") {
    type T = (TBuilderInstruction, Seq[TBuilderInstruction])

    type TParam = (TlaType1, Seq[TlaType1])

    implicit val typeSeqGen: Gen[TParam] = for {
      t <- singleTypeGen
      n <- Gen.choose(0, 5)
      seq <- Gen.listOfN(n, singleTypeGen)
    } yield (t, seq)

    def mkWellTyped(tparam: TParam): T = {
      val (t, ts) = tparam
      (
          builder.name("A", OperT1(ts, t)),
          ts.zipWithIndex.map { case (tt, i) =>
            builder.name(s"x$i", tt)
          },
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (t, ts) = tparam
      ts.indices.flatMap { i =>
        val badIth = ts.zipWithIndex.map { case (tt, j) =>
          if (i == j) InvalidTypeMethods.differentFrom(tt) else tt
        }
        Seq(
            (
                builder.name("A", OperT1(badIth, t)),
                ts.zipWithIndex.map { case (tt, i) =>
                  builder.name(s"x$i", tt)
                },
            ),
            (
                builder.name("A", OperT1(ts, t)),
                badIth.zipWithIndex.map { case (tt, i) =>
                  builder.name(s"x$i", tt)
                },
            ),
        )
      }
    }

    val resultIsExpected = expectEqTyped[TParam, T](
        TlaOper.apply,
        mkWellTyped,
        { case (a, seq) => liftBuildToSeq(a +: seq) },
        { case (t, _) => t },
    )

    checkRun(
        runVariadicWithDistinguishedFirst(
            builder.appOp,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("choose3") {
    type T = (TBuilderInstruction, TBuilderInstruction, TBuilderInstruction)
    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("x", tt),
          builder.name("set", SetT1(tt)),
          builder.name("p", BoolT1),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("x", InvalidTypeMethods.differentFrom(tt)),
              builder.name("set", SetT1(tt)),
              builder.name("p", BoolT1),
          ),
          (
              builder.name("x", tt),
              builder.name("set", SetT1(InvalidTypeMethods.differentFrom(tt))),
              builder.name("p", BoolT1),
          ),
          (
              builder.name("x", tt),
              builder.name("set", InvalidTypeMethods.notSet),
              builder.name("p", BoolT1),
          ),
          (
              builder.name("x", tt),
              builder.name("set", SetT1(tt)),
              builder.name("p", InvalidTypeMethods.notBool),
          ),
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaOper.chooseBounded,
        mkWellTyped,
        { case (a, b, c) => Seq(a, b, c) },
        tt => tt,
    )

    checkRun(
        runTernary(
            builder.choose,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("choose2") {
    type T = (TBuilderInstruction, TBuilderInstruction)
    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("x", tt),
          builder.name("p", BoolT1),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("x", tt),
              builder.name("p", InvalidTypeMethods.notBool),
          )
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaOper.chooseUnbounded,
        mkWellTyped,
        { case (a, b) => Seq(a, b) },
        tt => tt,
    )

    checkRun(
        runBinary(
            builder.choose,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("label") {
    type T = (TBuilderInstruction, Seq[String])

    type TParam = (TlaType1, Int)

    implicit val typeSeqGen: Gen[TParam] = for {
      t <- singleTypeGen
      n <- Gen.choose(1, 5)
    } yield (t, n)

    def mkWellTyped(tparam: TParam): T = {
      val (t, n) = tparam
      (
          builder.name("ex", t),
          (0 until n).map { i =>
            s"x$i"
          },
      )
    }

    def mkIllTyped(@unused tparam: TParam): Seq[T] = Seq.empty

    val resultIsExpected = expectEqTyped[TParam, T](
        TlaOper.label,
        mkWellTyped,
        { case (a, seq) => liftBuildToSeq(a +: seq.map { builder.str }) },
        { case (t, _) => t },
    )

    checkRun(
        runVariadicWithDistinguishedFirst(
            builder.label,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.label(builder.name("ex", IntT1)))
    }
  }

}
