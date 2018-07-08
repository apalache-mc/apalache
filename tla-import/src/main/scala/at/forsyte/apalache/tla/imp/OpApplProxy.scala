package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.predef.{TlaIntSet, TlaNatSet, TlaRealSet}
import at.forsyte.apalache.tla.lir.values.TlaRealInfinity
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, TlaValue, ValEx}
import tla2sany.semantic._

/**
  * This class acts as a proxy for OpAllTranslator. It hijacks the node that corresponds to the standard library
  * operators and translates them differently from the user operators.
  *
  * @author konnov
  */
class OpApplProxy(standardTranslator: OpApplTranslator) {
  def translate(node: OpApplNode): TlaEx = {
    node.getOperator match {
      case opdef: OpDefOrDeclNode if opdef.getKind == ASTConstants.UserDefinedOpKind =>
        if (opdef.getOriginallyDefinedInModuleNode != null) {
          val origin = opdef.getOriginallyDefinedInModuleNode
          val modAndName = (origin.getName.toString, opdef.getName.toString)
          OpApplProxy.libraryValues.get(modAndName) match {
            case Some(value: TlaValue) =>
              ValEx(value)

            case _ =>
              OpApplProxy.libraryOperators.get(modAndName) match {
                case Some(oper: TlaOper) =>
                  val exTran = ExprOrOpArgNodeTranslator(standardTranslator.context, standardTranslator.recStatus)
                  OperEx(oper, node.getArgs.map { p => exTran.translate(p)} :_*)

                case _ =>
                  standardTranslator.translate(node)
              }
          }
        } else {
          standardTranslator.translate(node)
        }

      case _ =>
        standardTranslator.translate(node)
    }
  }
}

object OpApplProxy {
  def apply(standardTranslator: OpApplTranslator): OpApplProxy = {
    new OpApplProxy(standardTranslator)
  }

  val libraryValues: Map[Tuple2[String, String], TlaValue] =
    Map(
      (("Naturals", "Nat"), TlaNatSet),
      (("Integers", "Int"), TlaIntSet),
      (("Reals", "Real"), TlaRealSet),
      (("Reals", "Infinity"), TlaRealInfinity)
    )

  val libraryOperators: Map[Tuple2[String, String], TlaOper] =
    Map(
      (("Naturals", "+"), TlaArithOper.plus),
      (("Naturals", "-"), TlaArithOper.minus),
      (("Naturals", "*"), TlaArithOper.mult),
      (("Naturals", "^"), TlaArithOper.exp),
      (("Naturals", "<"), TlaArithOper.lt),
      (("Naturals", ">"), TlaArithOper.gt),
      (("Naturals", "<="), TlaArithOper.le),
      (("Naturals", "\\leq"), TlaArithOper.le),
      (("Naturals", ">="), TlaArithOper.ge),
      (("Naturals", "\\geq"), TlaArithOper.ge),
      (("Naturals", "%"), TlaArithOper.mod),
      (("Naturals", "\\div"), TlaArithOper.realDiv),
      (("Naturals", ".."), TlaArithOper.dotdot),
      (("Integers", "-."), TlaArithOper.uminus),
      (("Reals", "/"), TlaArithOper.realDiv),
      (("Sequences", "Seq"), TlaSetOper.seqSet),
      (("Sequences", "Len"), TlaSeqOper.len),
      (("Sequences", "\\o"), TlaSeqOper.concat),
      (("Sequences", "Append"), TlaSeqOper.append),
      (("Sequences", "Head"), TlaSeqOper.head),
      (("Sequences", "Tail"), TlaSeqOper.tail),
      (("Sequences", "SubSeq"), TlaSeqOper.subseq),
      (("Sequences", "SelectSeq"), TlaSeqOper.selectseq),
      (("FiniteSets", "IsFiniteSet"), TlaFiniteSetOper.isFiniteSet),
      (("FiniteSets", "Cardinality"), TlaFiniteSetOper.cardinality),
      (("TLC", "Any"), TlcOper.any),
      (("TLC", "Assert"), TlcOper.assert),
      (("TLC", "@@"), TlcOper.atat),
      (("TLC", ":>"), TlcOper.colonGreater),
      (("TLC", "JavaTime"), TlcOper.javaTime),
      (("TLC", "Permutations"), TlcOper.permutations),
      (("TLC", "RandomElement"), TlcOper.randomElement),
      (("TLC", "SortSeq"), TlcOper.sortSeq),
      (("TLC", "TLCEval"), TlcOper.tlcEval),
      (("TLC", "TLCGet"), TlcOper.tlcGet),
      (("TLC", "TLCSet"), TlcOper.tlcSet),
      (("TLC", "ToString"), TlcOper.tlcToString),
      (("TLC", "Print"), TlcOper.print),
      (("TLC", "PrintT"), TlcOper.printT)
    )
}
