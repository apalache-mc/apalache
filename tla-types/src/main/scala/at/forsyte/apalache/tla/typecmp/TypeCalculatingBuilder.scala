package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaFunOper, TlaOper}

class TypeCalculatingBuilder(sigGen: SignatureGenerator) {

  // Build instruction for the case where the TNT operator has a signature, that is,
  // it is not overloaded. In that case, we just resolve signatures
  private def simpleInstruction(oper: TlaOper, nArgs: Int): BuildInstruction =
    BuildInstruction(oper, sigGen.computationFromSignature(oper, nArgs))

  def plus(x: TlaEx, y: TlaEx): TlaEx = {
    simpleInstruction(TlaArithOper.plus, 2).build(x, y)
  }

  def and(args: TlaEx*): TlaEx =
    BuildInstruction(TlaBoolOper.and, BoolOp.andCmp).build(args: _*)

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
