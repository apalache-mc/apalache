package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaFunOper, TlaOper}

object TypeCalculatingBuilder {

  def plus(x: TlaEx, y: TlaEx): TlaEx =
    BuildInstruction(TlaArithOper.plus, ArithOp.plusCmp).build(x, y)

  def and(args: TlaEx*): TlaEx =
    BuildInstruction(TlaBoolOper.and, BoolOp.andCmp).build(args: _*)

  def except(applicative: TlaEx, key1: TlaEx, val1: TlaEx, keysAndVals: TlaEx*) =
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
