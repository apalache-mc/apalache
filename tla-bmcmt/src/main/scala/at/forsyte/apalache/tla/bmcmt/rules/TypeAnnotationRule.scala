package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.oper.{BmcOper, TlaFunOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.predef.{TlaBoolSet, TlaIntSet, TlaStrSet}
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

import scala.collection.immutable.SortedMap

/**
  * This rule restricts a type of the subexpression with a type annotation.
  * The inferred type and the annotation should be unifiable, e.g., Set['a] and Set[Int].
  *
  * @author Igor Konnov
  */
class TypeAnnotationRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(BmcOper.withType, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(BmcOper.withType, subex, annotation) =>
        val rewrittenState = rewriter.rewriteUntilDone(state.setRex(subex).setTheory(CellTheory()))
        rewrittenState.ex match {
          case ex @ NameEx(name) if CellTheory().hasConst(name) =>
            val cell = rewrittenState.arena.findCellByNameEx(ex)
            val annotationType = parseAnnotation(annotation)
            val unifier = cell.cellType.unify(annotationType)
            unifier match {
              case Some(tp) =>
                // TODO: replace the type
                // FIXME: it's too late to replace the type as it has been propagated into SMT...
                rewriter.coerce(rewrittenState, state.theory) // coerce if needed

              case None =>
                throw new TypeException("No unifier for the annotation %s and the type %s"
                  .format(annotationType, cell.cellType))
            }


          case _ =>
            throw new RewriterException("%s: Expected a cell after rewriting, found: %s"
              .format(getClass.getSimpleName, rewrittenState.ex))
        }

      case e @ _ =>
        throw new RewriterException("%s is not applicable to %s".format(getClass.getSimpleName, e))
    }
  }

  private def parseAnnotation(annot: TlaEx): CellT = {
    annot match {
      case ValEx(TlaIntSet) =>
        IntT()

      case ValEx(TlaBoolSet) =>
        BoolT()

      case ValEx(TlaStrSet) =>
        ConstT()

      case OperEx(TlaSetOper.enumSet, elemAnnot: TlaEx) =>
        val elemType = parseAnnotation(elemAnnot)
        elemType match {
          case FunT(domT, resT) =>
            FinFunSetT(domT, FinSetT(resT)) // Is it correct? What if we have a powerset in the co-domain?

          case _ =>
            FinSetT(elemType)
        }

      case OperEx(TlaFunOper.enum, kv @ _*) =>
        val keys = kv.zipWithIndex.filter(_._2 % 2 == 0).map(_._1) // pick the even indices (starting with 0)
        def toStr(key: TlaEx) = key match {
          case ValEx(TlaStr(s)) => s
          case _ => throw new RewriterException("Expected a string, found: %s".format(key))
        }
        val vals = kv.zipWithIndex.filter(_._2 % 2 == 1).map(_._1) // pick the odd indices (starting with 0)
        val types = vals map parseAnnotation
        RecordT(SortedMap(keys.map(toStr).zip(types): _*))

      case OperEx(TlaFunOper.tuple, args @ _*) =>
        val types = args map parseAnnotation
        TupleT(types)

      case e =>
        throw new RewriterException("Unexpected type annotation: %s".format(annot))
    }
  }
}
