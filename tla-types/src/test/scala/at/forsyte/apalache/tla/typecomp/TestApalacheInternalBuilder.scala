package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{ApalacheInternalOper, TlaBoolOper, TlaOper, TlaSetOper}
import org.junit.runner.RunWith
import org.scalacheck.Prop.forAll
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

@RunWith(classOf[JUnitRunner])
class TestApalacheInternalBuilder extends BuilderTest {

  test("notSupportedByModelChecker") {

    val prop = forAll(singleTypeGen) { tt =>
      val notSuppEx: TlaEx = builder.notSupportedByModelChecker("msg", tt)
      notSuppEx.eqTyped(
          OperEx(
              ApalacheInternalOper.notSupportedByModelChecker,
              builder.str("msg"),
          )(Typed(tt))
      )
    }
    check(prop, minSuccessful(1000), sizeRange(8))
  }

  test("distinct") {
    type T = Seq[TBuilderInstruction]
    def mkWellTyped(n: Int)(tt: TlaType1): T =
      (1 to n).map { i => builder.name(s"x$i", tt) }
    def mkIllTyped(n: Int)(tt: TlaType1): Seq[T] =
      if (n > 1)
        (1 to n).map { j =>
          (1 to n).map { i =>
            if (i == j)
              builder.name(s"x$i", InvalidTypeMethods.differentFrom(tt))
            else
              builder.name(s"x$i", tt)
          }
        }
      else Seq.empty

    def resultIsExpected(n: Int) = expectEqTyped[TlaType1, T](
        ApalacheInternalOper.distinct,
        mkWellTyped(n),
        liftBuildToSeq,
        _ => BoolT1,
    )

    def run(tparam: TlaType1) = {
      (1 to 5).forall { n =>
        runVariadic[TlaType1, TBuilderInstruction](
            builder.distinct(_: _*),
            mkWellTyped(n),
            mkIllTyped(n),
            resultIsExpected(n),
        )(tparam)
      }
    }

    checkRun(run)

    // test fail on n = 0
    assertThrows[IllegalArgumentException] {
      build(builder.distinct())
    }
  }

  test("apalacheSeqCapacity") {
    type T = TBuilderInstruction

    def mkWellTyped(tt: TlaType1): T =
      builder.name("s", SeqT1(tt))
    def mkIllTyped(@unused tt: TlaType1): Seq[T] =
      Seq(
          builder.name("s", InvalidTypeMethods.notSeq)
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        ApalacheInternalOper.apalacheSeqCapacity,
        mkWellTyped,
        Seq(_),
        _ => IntT1,
    )

    checkRun(
        runUnary(
            builder.apalacheSeqCapacity,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("selectInSet/storeInSet2/storeNotInSet") {
    type T = (TBuilderInstruction, TBuilderInstruction)

    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("x", tt),
          builder.name("S", SetT1(tt)),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("x", InvalidTypeMethods.differentFrom(tt)),
              builder.name("S", SetT1(tt)),
          ),
          (
              builder.name("x", tt),
              builder.name("S", SetT1(InvalidTypeMethods.differentFrom(tt))),
          ),
          (
              builder.name("x", tt),
              builder.name("S", InvalidTypeMethods.notSet),
          ),
      )

    def resultIsExpected(oper: ApalacheInternalOper) = expectEqTyped[TlaType1, T](
        oper,
        mkWellTyped,
        { case (a, b) => Seq(a, b) },
        _ => BoolT1,
    )

    def run(oper: ApalacheInternalOper, method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction) =
      runBinary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(oper),
      )(_)

    checkRun(run(ApalacheInternalOper.selectInSet, builder.selectInSet))
    checkRun(run(ApalacheInternalOper.storeInSet, builder.storeInSet))
    checkRun(run(ApalacheInternalOper.storeNotInSet, builder.storeNotInSet))
  }

  test("storeInSet3") {
    type T = (TBuilderInstruction, TBuilderInstruction, TBuilderInstruction)
    type TParam = (TlaType1, TlaType1)

    def mkWellTyped(tparam: TParam): T = {
      val (a, b) = tparam
      (
          builder.name("y", b),
          builder.name("f", FunT1(a, b)),
          builder.name("x", a),
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (a, b) = tparam
      Seq(
          (
              builder.name("y", InvalidTypeMethods.differentFrom(b)),
              builder.name("f", FunT1(a, b)),
              builder.name("x", a),
          ),
          (
              builder.name("y", b),
              builder.name("f", FunT1(InvalidTypeMethods.differentFrom(a), b)),
              builder.name("x", a),
          ),
          (
              builder.name("y", b),
              builder.name("f", FunT1(a, InvalidTypeMethods.differentFrom(b))),
              builder.name("x", a),
          ),
          (
              builder.name("y", b),
              builder.name("f", FunT1(a, b)),
              builder.name("x", InvalidTypeMethods.differentFrom(a)),
          ),
      )
    }

    def resultIsExpected = expectEqTyped[TParam, T](
        ApalacheInternalOper.storeInSet,
        mkWellTyped,
        { case (a, b, c) => Seq(a, b, c) },
        _ => BoolT1,
    )

    checkRun(
        runTernary(
            builder.storeInSet,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

  test("smtMap") {
    type T = (TBuilderInstruction, TBuilderInstruction)

    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("S", SetT1(tt)),
          builder.name("T", SetT1(tt)),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("S", SetT1(InvalidTypeMethods.differentFrom(tt))),
              builder.name("T", SetT1(tt)),
          ),
          (
              builder.name("S", SetT1(tt)),
              builder.name("T", SetT1(InvalidTypeMethods.differentFrom(tt))),
          ),
          (
              builder.name("S", InvalidTypeMethods.notSet),
              builder.name("T", SetT1(tt)),
          ),
          (
              builder.name("S", SetT1(tt)),
              builder.name("T", InvalidTypeMethods.notSet),
          ),
      )

    def resultIsExpected(oper: TlaOper) = expectEqTyped[TlaType1, T](
        ApalacheInternalOper.smtMap(oper),
        mkWellTyped,
        { case (a, b) => Seq(a, b) },
        tt => SetT1(tt),
    )

    def run(oper: TlaOper) =
      runBinary(
          builder.smtMap(oper, _, _),
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(oper),
      )(_)

    checkRun(run(TlaBoolOper.and))
    checkRun(run(TlaBoolOper.or))

    // Throws on TlaOper not supported by smtMap
    assertThrows[TBuilderTypeException] {
      build(
          builder.smtMap(
              TlaSetOper.union,
              builder.name("S", SetT1(IntT1)),
              builder.name("T", SetT1(IntT1)),
          )
      )
    }
  }

  test("unconstrainArraySig") {
    type T = TBuilderInstruction

    def mkWellTyped(tt: TlaType1): T =
      builder.name("S", SetT1(tt))
    def mkIllTyped(@unused tt: TlaType1): Seq[T] =
      Seq(
          builder.name("S", InvalidTypeMethods.notSet)
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        ApalacheInternalOper.unconstrainArray,
        mkWellTyped,
        Seq(_),
        _ => BoolT1,
    )

    checkRun(
        runUnary(
            builder.unconstrainArray,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

}
