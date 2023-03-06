package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTupledBuilder extends BuilderTest {

  test("(forall/exists)AllowTuples3") {
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

    checkRun(Generators.typeAndSeqGen)(run(TlaBoolOper.forall, builder.forallAllowTuples))
    assertThrowsBoundVarIntroductionTernary(builder.forallAllowTuples)

    checkRun(Generators.typeAndSeqGen)(run(TlaBoolOper.exists, builder.existsAllowTuples))
    assertThrowsBoundVarIntroductionTernary(builder.existsAllowTuples)
  }

  test("(forall/exists)AllowTuples2") {
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

    checkRun(Generators.typeAndSeqGen)(run(TlaBoolOper.forallUnbounded, builder.forallAllowTuples))
    assertThrowsBoundVarIntroductionTernary(builder.forallAllowTuples)

    checkRun(Generators.typeAndSeqGen)(run(TlaBoolOper.existsUnbounded, builder.existsAllowTuples))
    assertThrowsBoundVarIntroductionTernary(builder.existsAllowTuples)
  }
}
