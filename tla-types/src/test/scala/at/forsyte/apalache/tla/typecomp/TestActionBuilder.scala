package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import org.junit.runner.RunWith
import org.scalacheck.Gen
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

@RunWith(classOf[JUnitRunner])
class TestActionBuilder extends BuilderTest {

  test("prime") {
    type T = TBuilderInstruction
    def mkWellTyped(tt: TlaType1): T = builder.name("x", tt)

    def mkIllTyped(@unused tt: TlaType1): Seq[T] = Seq.empty

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaActionOper.prime,
        mkWellTyped,
        ToSeq.unary,
        tt => tt,
    )

    checkRun(
        runUnary(
            builder.prime,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )(Generators.singleTypeGen)
  }

  test("stutt/nostutt") {
    type T = (TBuilderInstruction, TBuilderInstruction)
    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("A", BoolT1),
          builder.name("e", tt),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("A", InvalidTypeMethods.notBool),
              builder.name("e", tt),
          )
      )

    def resultIsExpected(op: TlaActionOper) = expectEqTyped[TlaType1, T](
        op,
        mkWellTyped,
        ToSeq.binary,
        _ => BoolT1,
    )

    def run(
        op: TlaActionOper,
        method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction,
      )(tt: TlaType1): Boolean =
      runBinary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(op),
      )(tt)

    checkRun(run(TlaActionOper.stutter, builder.stutt))(Generators.singleTypeGen)
    checkRun(run(TlaActionOper.nostutter, builder.nostutt))(Generators.singleTypeGen)
  }

  test("enabled") {

    type T = TBuilderInstruction
    def mkWellTyped(@unused tt: Unit): T = builder.name("A", BoolT1)

    def mkIllTyped(@unused tt: Unit): Seq[T] =
      Seq(
          builder.name("A", InvalidTypeMethods.notBool)
      )

    def resultIsExpected = expectEqTyped[Unit, T](
        TlaActionOper.enabled,
        mkWellTyped,
        ToSeq.unary,
        _ => BoolT1,
    )

    checkRun(
        runUnary(
            builder.enabled,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )(Generators.unitGen)
  }

  test("unchanged") {
    type T = TBuilderInstruction
    def mkWellTyped(tt: TlaType1): T = builder.name("e", tt)

    def mkIllTyped(@unused tt: TlaType1): Seq[T] = Seq.empty

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaActionOper.unchanged,
        mkWellTyped,
        ToSeq.unary,
        _ => BoolT1,
    )

    checkRun(
        runUnary(
            builder.unchanged,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )(Generators.singleTypeGen)
  }

  test("cmp") {
    type T = (TBuilderInstruction, TBuilderInstruction)
    def mkWellTyped(@unused tt: Unit): T =
      (
          builder.name("A", BoolT1),
          builder.name("B", BoolT1),
      )

    def mkIllTyped(@unused tt: Unit): Seq[T] =
      Seq(
          (
              builder.name("A", InvalidTypeMethods.notBool),
              builder.name("B", BoolT1),
          ),
          (
              builder.name("A", BoolT1),
              builder.name("B", InvalidTypeMethods.notBool),
          ),
      )

    def resultIsExpected = expectEqTyped[Unit, T](
        TlaActionOper.composition,
        mkWellTyped,
        ToSeq.binary,
        _ => BoolT1,
    )

    checkRun(
        runBinary(
            builder.comp,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )(Generators.unitGen)
  }

}
