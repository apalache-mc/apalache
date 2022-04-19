package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.typecmp.raw.{ProtoBuilder, RawArithmeticBuilder, RawBoolBuilder}

// IGNORE, WIP artifact
class TypeCalculatingBuilder(val sigGen: SignatureGenerator)
    extends ProtoBuilder with RawArithmeticBuilder with RawBoolBuilder {

  def except(
      applicative: TlaEx,
      key1: TlaEx,
      val1: TlaEx,
      keysAndVals: TlaEx*) =
    BuildInstruction(TlaFunOper.except, FunOp.exceptCmp).build(applicative +: key1 +: val1 +: keysAndVals: _*)

  def seq(head: TlaEx, tail: TlaEx*) =
    BuildInstruction(TlaFunOper.tuple, FunOp.seqCmp).build(head +: tail: _*)

  def emptySeq(seqElemType: TlaType1) =
    OperEx(TlaFunOper.tuple)(Typed(SeqT1(seqElemType)))

  def tuple(args: TlaEx*) =
    BuildInstruction(TlaFunOper.tuple, FunOp.tupCmp).build(args: _*)

  def emptyTup() =
    OperEx(TlaFunOper.tuple)(Typed(TupT1()))

}
