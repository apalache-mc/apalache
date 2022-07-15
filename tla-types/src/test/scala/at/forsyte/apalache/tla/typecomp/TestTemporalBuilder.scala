package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaTempOper
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTemporalBuilder extends BuilderTest {

  test("box/diamond") {

    type T = TBuilderInstruction

    def mkWellTyped: Unit => T = _ => builder.name("P", BoolT1)
    def mkIllTyped: Unit => Seq[T] = _ =>
      Seq(
          builder.name("P", InvalidTypeMethods.notBool)
      )

    def resultIsExpected(oper: TlaTempOper) = expectEqTyped[Unit, T](
        oper,
        mkWellTyped,
        ToSeq.unary,
        { _ => BoolT1 },
    )

    def run(oper: TlaTempOper, method: TBuilderInstruction => TBuilderInstruction) =
      runUnary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(oper),
      )(_)

    assert(run(TlaTempOper.box, builder.box)(()))
    assert(run(TlaTempOper.diamond, builder.diamond)(()))
  }

  test("leadsTo/guarantees") {

    type T = (TBuilderInstruction, TBuilderInstruction)

    def mkWellTyped: Unit => T = _ =>
      (
          builder.name("P", BoolT1),
          builder.name("Q", BoolT1),
      )
    def mkIllTyped: Unit => Seq[T] = _ =>
      Seq(
          (
              builder.name("P", InvalidTypeMethods.notBool),
              builder.name("Q", BoolT1),
          ),
          (
              builder.name("P", BoolT1),
              builder.name("Q", InvalidTypeMethods.notBool),
          ),
      )

    def resultIsExpected(oper: TlaTempOper) = expectEqTyped[Unit, T](
        oper,
        mkWellTyped,
        ToSeq.binary,
        { _ => BoolT1 },
    )

    def run(oper: TlaTempOper, method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction) =
      runBinary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(oper),
      )(_)

    assert(run(TlaTempOper.leadsTo, builder.leadsTo)(()))
    assert(run(TlaTempOper.guarantees, builder.guarantees)(()))
  }

  test("WF/SF") {

    type T = (TBuilderInstruction, TBuilderInstruction)

    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("x", tt),
          builder.name("A", BoolT1),
      )
    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("x", tt),
              builder.name("A", InvalidTypeMethods.notBool),
          )
      )

    def resultIsExpected(oper: TlaTempOper) = expectEqTyped[TlaType1, T](
        oper,
        mkWellTyped,
        ToSeq.binary,
        { _ => BoolT1 },
    )

    def run(oper: TlaTempOper, method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction) =
      runBinary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(oper),
      )(_)

    checkRun(Generators.singleTypeGen)(run(TlaTempOper.strongFairness, builder.SF))
    checkRun(Generators.singleTypeGen)(run(TlaTempOper.weakFairness, builder.WF))
  }

  test("AA/EE") {
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

    def resultIsExpected(oper: TlaTempOper) = expectEqTyped[TlaType1, T](
        oper,
        mkWellTyped,
        ToSeq.binary,
        _ => BoolT1,
    )

    def run(oper: TlaTempOper, method: (TBuilderInstruction, TBuilderInstruction) => TBuilderInstruction) =
      runBinary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(oper),
      )(_)

    checkRun(Generators.singleTypeGen)(run(TlaTempOper.AA, builder.AA))
    checkRun(Generators.singleTypeGen)(run(TlaTempOper.EE, builder.EE))

    assertThrowsBoundVarIntroductionBinary(builder.AA)
    assertThrowsBoundVarIntroductionBinary(builder.EE)
  }

}
