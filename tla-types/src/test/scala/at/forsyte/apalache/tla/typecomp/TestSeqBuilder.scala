package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaSeqOper
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner
import scalaz.unused

@RunWith(classOf[JUnitRunner])
class TestSeqBuilder extends BuilderTest {

  test("append") {
    type T = (TBuilderInstruction, TBuilderInstruction)
    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("seq", SeqT1(tt)),
          builder.name("e", tt),
      )
    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("seq", InvalidTypeMethods.notSeq),
              builder.name("e", tt),
          ),
          (
              builder.name("seq", SeqT1(tt)),
              builder.name("e", InvalidTypeMethods.differentFrom(tt)),
          ),
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaSeqOper.append,
        mkWellTyped,
        ToSeq.binary,
        tt => SeqT1(tt),
    )

    checkRun(Generators.singleTypeGen)(
        runBinary(
            builder.append,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("concat") {
    type T = (TBuilderInstruction, TBuilderInstruction)
    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("seq1", SeqT1(tt)),
          builder.name("seq2", SeqT1(tt)),
      )
    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("seq1", InvalidTypeMethods.notSeq),
              builder.name("seq2", SeqT1(tt)),
          ),
          (
              builder.name("seq1", SeqT1(tt)),
              builder.name("seq2", SeqT1(InvalidTypeMethods.differentFrom(tt))),
          ),
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaSeqOper.concat,
        mkWellTyped,
        ToSeq.binary,
        tt => SeqT1(tt),
    )

    checkRun(Generators.singleTypeGen)(
        runBinary(
            builder.concat,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )

  }

  test("head/tail/len") {
    type T = TBuilderInstruction
    def mkWellTyped(tt: TlaType1): T =
      builder.name("seq", SeqT1(tt))

    def mkIllTyped(@unused tt: TlaType1): Seq[T] =
      Seq(
          builder.name("seq", InvalidTypeMethods.notSeq)
      )

    def resultIsExpected(op: TlaSeqOper, corrType: TlaType1 => TlaType1) = expectEqTyped[TlaType1, T](
        op,
        mkWellTyped,
        ToSeq.unary,
        corrType,
    )

    def run(
        op: TlaSeqOper,
        corrType: TlaType1 => TlaType1,
        method: TBuilderInstruction => TBuilderInstruction,
      )(tt: TlaType1): Boolean =
      runUnary(
          method,
          mkWellTyped,
          mkIllTyped,
          resultIsExpected(op, corrType),
      )(tt)

    checkRun(Generators.singleTypeGen)(run(TlaSeqOper.head, tt => tt, builder.head))

    checkRun(Generators.singleTypeGen)(run(TlaSeqOper.tail, tt => SeqT1(tt), builder.tail))

    checkRun(Generators.singleTypeGen)(run(TlaSeqOper.len, _ => IntT1, builder.len))
  }

  test("subseq") {
    type T = (TBuilderInstruction, TBuilderInstruction, TBuilderInstruction)
    def mkWellTyped(tt: TlaType1): T =
      (
          builder.name("seq", SeqT1(tt)),
          builder.name("m", IntT1),
          builder.name("n", IntT1),
      )

    def mkIllTyped(tt: TlaType1): Seq[T] =
      Seq(
          (
              builder.name("seq", InvalidTypeMethods.notSeq),
              builder.name("m", IntT1),
              builder.name("n", IntT1),
          ),
          (
              builder.name("seq", SeqT1(tt)),
              builder.name("m", InvalidTypeMethods.notInt),
              builder.name("n", IntT1),
          ),
          (
              builder.name("seq", SeqT1(tt)),
              builder.name("m", IntT1),
              builder.name("n", InvalidTypeMethods.notInt),
          ),
      )

    def resultIsExpected = expectEqTyped[TlaType1, T](
        TlaSeqOper.subseq,
        mkWellTyped,
        ToSeq.ternary,
        tt => SeqT1(tt),
    )

    checkRun(Generators.singleTypeGen)(
        runTernary(
            builder.subseq,
            mkWellTyped,
            mkIllTyped,
            resultIsExpected,
        )
    )
  }

}
