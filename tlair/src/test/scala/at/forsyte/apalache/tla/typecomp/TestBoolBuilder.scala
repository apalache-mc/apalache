package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

@RunWith(classOf[JUnitRunner])
class TestBoolBuilder extends BuilderTest {

  test("and/or") {
    type T = Seq[TBuilderInstruction]
    type TParam = Int

    def mkWellTyped(tparam: TParam): T =
      (0 until tparam).map { i =>
        builder.name(s"x$i", BoolT1)
      }

    def mkIllTyped(tparam: TParam): Seq[T] =
      (0 until tparam).map { j =>
        (0 until tparam).map { i =>
          builder.name(s"x$i", if (i == j) InvalidTypeMethods.notBool else BoolT1)
        }
      }

    def resultIsExpected(oper: TlaBoolOper) = expectEqTyped[TParam, T](
        oper,
        mkWellTyped,
        ToSeq.variadic,
        _ => BoolT1,
    )

    def run(oper: TlaBoolOper, method: T => TBuilderInstruction) =
      runVariadic(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(oper),
      ) _

    checkRun(Generators.nonNegativeIntGen)(run(TlaBoolOper.and, builder.and))
    checkRun(Generators.nonNegativeIntGen)(run(TlaBoolOper.or, builder.or))

  }

  test("not") {
    type T = TBuilderInstruction
    type TParam = Unit

    def mkWellTyped(@unused tparam: TParam): T = builder.name("x", BoolT1)

    def mkIllTyped(@unused tparam: TParam): Seq[T] =
      Seq(
          builder.name("x", InvalidTypeMethods.notBool)
      )

    def resultIsExpected = expectEqTyped[TParam, T](
        TlaBoolOper.not,
        mkWellTyped,
        ToSeq.unary,
        _ => BoolT1,
    )

    checkRun(Generators.unitGen)(
        runUnary(
            builder.not,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("impl/equiv") {
    type T = (TBuilderInstruction, TBuilderInstruction)
    type TParam = Unit

    def mkWellTyped(@unused tparam: TParam): T =
      (
          builder.name("x", BoolT1),
          builder.name("y", BoolT1),
      )

    def mkIllTyped(@unused tparam: TParam): Seq[T] =
      Seq(
          (
              builder.name("x", BoolT1),
              builder.name("y", InvalidTypeMethods.notBool),
          ),
          (
              builder.name("x", InvalidTypeMethods.notBool),
              builder.name("y", BoolT1),
          ),
      )

    def resultIsExpected(oper: TlaBoolOper) = expectEqTyped[TParam, T](
        oper,
        mkWellTyped,
        ToSeq.binary,
        _ => BoolT1,
    )

    def run(oper: TlaBoolOper, method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction) =
      runBinary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(oper),
      ) _

    checkRun(Generators.unitGen)(run(TlaBoolOper.implies, builder.impl))
    checkRun(Generators.unitGen)(run(TlaBoolOper.equiv, builder.equiv))
  }

  test("forall3/exists3") {
    type T = (TBuilderInstruction, TBuilderInstruction, TBuilderInstruction)
    type TParam = (TlaType1, Seq[TlaType1])

    def mkWellTyped(tparam: TParam): T = {
      val (t, ts) = tparam
      val tt = if (ts.isEmpty) t else TupT1(ts: _*)
      (
          builder.name("x", tt),
          builder.name("set", SetT1(tt)),
          builder.name("p", BoolT1),
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (t, ts) = tparam
      val tt = if (ts.isEmpty) t else TupT1(ts: _*)
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
    }

    def resultIsExpected(oper: TlaBoolOper) = expectEqTyped[TParam, T](
        oper,
        mkWellTyped,
        ToSeq.ternary,
        _ => BoolT1,
    )

    def run(
        oper: TlaBoolOper,
        method: (TBuilderInstruction, TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction) =
      runTernary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(oper),
      ) _

    checkRun(Generators.typeAndSeqGen)(run(TlaBoolOper.forall, builder.forall))
    assertThrowsBoundVarIntroductionTernary(builder.forall)
    assertThrowsBoundVarIntroductionTernaryTupled(builder.forall)

    checkRun(Generators.typeAndSeqGen)(run(TlaBoolOper.exists, builder.exists))
    assertThrowsBoundVarIntroductionTernary(builder.exists)
    assertThrowsBoundVarIntroductionTernaryTupled(builder.exists)

  }

  test("forall2/exists2") {
    type T = (TBuilderInstruction, TBuilderInstruction)
    type TParam = (TlaType1, Seq[TlaType1])

    def mkWellTyped(tparam: TParam): T = {
      val (t, ts) = tparam
      val tt = if (ts.isEmpty) t else TupT1(ts: _*)
      (
          builder.name("x", tt),
          builder.name("p", BoolT1),
      )
    }

    def mkIllTyped(tparam: TParam): Seq[T] = {
      val (t, ts) = tparam
      val tt = if (ts.isEmpty) t else TupT1(ts: _*)
      Seq(
          (
              builder.name("x", tt),
              builder.name("p", InvalidTypeMethods.notBool),
          )
      )
    }

    def resultIsExpected(oper: TlaBoolOper) = expectEqTyped[TParam, T](
        oper,
        mkWellTyped,
        ToSeq.binary,
        _ => BoolT1,
    )

    def run(
        oper: TlaBoolOper,
        method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction) =
      runBinary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(oper),
      ) _

    checkRun(Generators.typeAndSeqGen)(run(TlaBoolOper.forallUnbounded, builder.forall))
    assertThrowsBoundVarIntroductionBinary(builder.forall)
    assertThrowsBoundVarIntroductionBinaryTupled(builder.forall)

    checkRun(Generators.typeAndSeqGen)(run(TlaBoolOper.existsUnbounded, builder.exists))
    assertThrowsBoundVarIntroductionBinary(builder.exists)
    assertThrowsBoundVarIntroductionBinaryTupled(builder.exists)
  }
}
