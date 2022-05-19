package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaControlOper
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestControlBuilder extends BuilderTest {

  test("ite") {
    type T = (TBuilderInstruction, TBuilderInstruction, TBuilderInstruction)
    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("p", BoolT1),
          builder.name("A", tt),
          builder.name("B", tt),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("p", InvalidTypeMethods.notBool),
              builder.name("A", tt),
              builder.name("B", tt),
          ),
          (
              builder.name("p", BoolT1),
              builder.name("A", InvalidTypeMethods.differentFrom(tt)),
              builder.name("B", tt),
          ),
          (
              builder.name("p", BoolT1),
              builder.name("A", tt),
              builder.name("B", InvalidTypeMethods.differentFrom(tt)),
          ),
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaControlOper.ifThenElse,
        mkWellTyped,
        { case (a, b, c) => Seq(a, b, c) },
        tt => tt,
    )

    checkRun(
        runTernary(
            builder.ite,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("caseNoOther") {
    type T = Seq[(TBuilderInstruction, TBuilderInstruction)]

    type TParam = (TlaType1, Int)

    implicit val typeSeqGen: Gen[TParam] = for {
      t <- singleTypeGen
      n <- Gen.choose(1, 5)
    } yield (t, n)

    def mkWellTyped(tparam: TParam): T = {
      val (t, n) = tparam
      (1 to n).map { i =>
        (
            builder.name(s"p$i", BoolT1),
            builder.name(s"e$i", t),
        )
      }
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (t, n) = tparam
      (1 to n).flatMap { j =>
        val bodyFuzzOpt =
          if (n > 1) // If there's only 1 case branch, the body can't be ill-typed
            Some(
                (1 to n).map { i =>
                  (
                      builder.name(s"p$i", BoolT1),
                      builder.name(s"e$i", if (i == j) InvalidTypeMethods.differentFrom(t) else t),
                  )
                }
            )
          else None

        bodyFuzzOpt ++:
          Seq(
              (1 to n).map { i =>
                (
                    builder.name(s"p$i", if (i == j) InvalidTypeMethods.notBool else BoolT1),
                    builder.name(s"e$i", t),
                )
              }
          )
      }
    }

    val resultIsExpected = expectEqTyped[TParam, T](
        TlaControlOper.caseNoOther,
        mkWellTyped,
        { seq => liftBuildToSeq(seq.flatMap { case (a, b) => Seq(a, b) }) },
        { case (t, _) => t },
    )

    checkRun(
        runVariadic(
            builder.caseSplit,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.caseSplit())
    }

    // Mixed
    type T2 = Seq[TBuilderInstruction]

    def mkWellTyped2(tparam: TParam): T2 = {
      val (t, n) = tparam
      (1 to n).flatMap { i =>
        Seq(
            builder.name(s"p$i", BoolT1),
            builder.name(s"e$i", t),
        )
      }
    }

    def mkIllTyped2(tparam: TParam): Seq[T2] = {
      val (t, n) = tparam
      (1 to n).flatMap { j =>
        val bodyFuzzOpt =
          if (n > 1)
            Some(
                (1 to n).flatMap { i =>
                  Seq(
                      builder.name(s"p$i", BoolT1),
                      builder.name(s"e$i", if (i == j) InvalidTypeMethods.differentFrom(t) else t),
                  )
                }
            )
          else None

        bodyFuzzOpt ++:
          Seq(
              (1 to n).flatMap { i =>
                Seq(
                    builder.name(s"p$i", if (i == j) InvalidTypeMethods.notBool else BoolT1),
                    builder.name(s"e$i", t),
                )
              }
          )
      }
    }

    val resultIsExpected2 = expectEqTyped[TParam, T2](
        TlaControlOper.caseNoOther,
        mkWellTyped2,
        liftBuildToSeq,
        { case (t, _) => t },
    )

    checkRun(
        runVariadic(
            builder.caseSplitMixed,
            mkWellTyped2,
            mkIllTyped2,
            resultIsExpected2,
        )
    )

    // test fail on n = 0 or odd nArgs
    assertThrows[IllegalArgumentException] {
      build(builder.caseSplitMixed())
    }

    assertThrows[IllegalArgumentException] {
      build(builder.caseSplitMixed(builder.name("x", BoolT1)))
    }
  }

  test("caseWithOther") {
    type T = (TBuilderInstruction, Seq[(TBuilderInstruction, TBuilderInstruction)])

    type TParam = (TlaType1, Int)

    implicit val typeSeqGen: Gen[TParam] = for {
      t <- singleTypeGen
      n <- Gen.choose(1, 5)
    } yield (t, n)

    def mkWellTyped(tparam: TParam): T = {
      val (t, n) = tparam
      val pairs = (1 to n).map { i =>
        (
            builder.name(s"p$i", BoolT1),
            builder.name(s"e$i", t),
        )
      }

      (builder.name("e", t), pairs)
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (t, n) = tparam
      (
          builder.name("e", InvalidTypeMethods.differentFrom(t)),
          (1 to n).map { i =>
            (
                builder.name(s"p$i", BoolT1),
                builder.name(s"e$i", t),
            )
          },
      ) +:
        (1 to n).flatMap { j =>
          val bodyFuzzOpt =
            if (n > 1) // If there's only 1 case branch, the body can't be ill-typed
              Some(
                  (
                      builder.name("e", t),
                      (1 to n).map { i =>
                        (
                            builder.name(s"p$i", BoolT1),
                            builder.name(s"e$i", if (i == j) InvalidTypeMethods.differentFrom(t) else t),
                        )
                      },
                  )
              )
            else None

          bodyFuzzOpt ++:
            Seq(
                (
                    builder.name("e", t),
                    (1 to n).map { i =>
                      (
                          builder.name(s"p$i", if (i == j) InvalidTypeMethods.notBool else BoolT1),
                          builder.name(s"e$i", t),
                      )
                    },
                )
            )
        }
    }

    val resultIsExpected = expectEqTyped[TParam, T](
        TlaControlOper.caseWithOther,
        mkWellTyped,
        { case (other, pairs) => liftBuildToSeq(other +: pairs.flatMap { case (a, b) => Seq(a, b) }) },
        { case (t, _) => t },
    )

    checkRun(
        runVariadicWithDistinguishedFirst(
            builder.caseOther,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.caseOther(builder.name("e", IntT1)))
    }

    // Mixed
    type T2 = (TBuilderInstruction, Seq[TBuilderInstruction])

    def mkWellTyped2(tparam: TParam): T2 = {
      val (t, n) = tparam
      (builder.name("e", t),
          (1 to n).flatMap { i =>
            Seq(
                builder.name(s"p$i", BoolT1),
                builder.name(s"e$i", t),
            )
          })
    }

    def mkIllTyped2(tparam: TParam): Seq[T2] = {
      val (t, n) = tparam
      (
          builder.name("e", InvalidTypeMethods.differentFrom(t)),
          (1 to n).flatMap { i =>
            Seq(
                builder.name(s"p$i", BoolT1),
                builder.name(s"e$i", t),
            )
          },
      ) +:
        (1 to n).flatMap { j =>
          val bodyFuzzOpt =
            if (n > 1)
              Some(
                  (
                      builder.name("e", t),
                      (1 to n).flatMap { i =>
                        Seq(
                            builder.name(s"p$i", BoolT1),
                            builder.name(s"e$i", if (i == j) InvalidTypeMethods.differentFrom(t) else t),
                        )
                      },
                  )
              )
            else None

          bodyFuzzOpt ++:
            Seq(
                (
                    builder.name("e", t),
                    (1 to n).flatMap { i =>
                      Seq(
                          builder.name(s"p$i", if (i == j) InvalidTypeMethods.notBool else BoolT1),
                          builder.name(s"e$i", t),
                      )
                    },
                )
            )
        }
    }

    val resultIsExpected2 = expectEqTyped[TParam, T2](
        TlaControlOper.caseWithOther,
        mkWellTyped2,
        { case (e, seq) => liftBuildToSeq(e +: seq) },
        { case (t, _) => t },
    )

    checkRun(
        runVariadicWithDistinguishedFirst(
            builder.caseOtherMixed,
            mkWellTyped2,
            mkIllTyped2,
            resultIsExpected2,
        )
    )

    // test fail on n = 0 or even nArgs
    assertThrows[IllegalArgumentException] {
      build(builder.caseOtherMixed(builder.name("e", BoolT1)))
    }

    assertThrows[IllegalArgumentException] {
      build(builder.caseOtherMixed(builder.name("e", BoolT1), builder.name("x", BoolT1)))
    }

  }

}
