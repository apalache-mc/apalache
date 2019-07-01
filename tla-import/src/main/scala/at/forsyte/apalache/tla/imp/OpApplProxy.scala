package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.{SourceLocation, SourceStore}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.predef.{TlaIntSet, TlaNatSet, TlaRealSet}
import at.forsyte.apalache.tla.lir.values.TlaRealInfinity
import tla2sany.semantic._

/**
  * This class acts as a proxy for OpAllTranslator. It hijacks the nodes that correspond to the standard library
  * operators and translates to the built-in operator objects.
  *
  * @author konnov
  */
class OpApplProxy(sourceStore: SourceStore, standardTranslator: OpApplTranslator) {
  def translate(node: OpApplNode): TlaEx = {
    node.getOperator match {
      case opdef: OpDefOrDeclNode if opdef.getKind == ASTConstants.UserDefinedOpKind =>
        if (opdef.getOriginallyDefinedInModuleNode != null) {
          val origin = opdef.getOriginallyDefinedInModuleNode
          val modAndName = (origin.getName.toString, opdef.getName.toString)
          OpApplProxy.libraryValues.get(modAndName) match {
            case Some(value: TlaValue) =>
              // a built-in value
              ValEx(value)

            case _ =>
              OpApplProxy.libraryOperators.get(modAndName) match {
                case Some(oper: TlaOper) =>
                  // an operator in the standard library
                  val exTran = ExprOrOpArgNodeTranslator(sourceStore, standardTranslator.context, standardTranslator.recStatus)
                  val resEx = OperEx(oper, node.getArgs.map { p => exTran.translate(p)} :_*)
                  // the source should point to the operator application, not the definition
                  // of the standard operator, which is pretty useless
                  sourceStore.addRec(resEx, SourceLocation(node.getLocation))

                case _ =>
                  OpApplProxy.globalOperators.get(opdef.getName.toString) match {
                    case Some(oper: TlaOper) =>
                      // an operator that we overwrite unconditionally, e.g., <:
                      val exTran = ExprOrOpArgNodeTranslator(sourceStore, standardTranslator.context, standardTranslator.recStatus)
                      val resEx = OperEx(oper, node.getArgs.map { p => exTran.translate(p) }: _*)
                      sourceStore.addRec(resEx, SourceLocation(node.getLocation))

                    case _ =>
                      standardTranslator.translate(node)
                  }
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
  def apply(sourceStore: SourceStore, standardTranslator: OpApplTranslator) : OpApplProxy = {
    new OpApplProxy(sourceStore, standardTranslator)
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
      (("Naturals", "\\div"), TlaArithOper.div),
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

  val globalOperators: Map[String, TlaOper] =
    Map[String, TlaOper](
      ("<:", BmcOper.withType)
    )
}
