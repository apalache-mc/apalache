package at.forsyte.apalache.tla.bmcmt.types

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.predef.{TlaBoolSet, TlaIntSet, TlaStrSet}
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, ValEx}

import scala.collection.immutable.SortedMap

/**
  * A parser for type annotations, which are written as TLA+ expressions.
  *
  * @author Igor Konnov
  */
object AnnotationParser {
  def parse(annot: TlaEx): CellT = {
    annot match {
      case ValEx(TlaIntSet) =>
        IntT()

      case ValEx(TlaBoolSet) =>
        BoolT()

      case ValEx(TlaStrSet) =>
        ConstT()

      case OperEx(TlaSetOper.enumSet, elemAnnot: TlaEx) =>
        val elemType = parse(elemAnnot)
        elemType match {
          case FunT(domT, resT) =>
            FinFunSetT(domT, FinSetT(resT)) // Is it correct? What if we have a powerset in the co-domain?

          case _ =>
            FinSetT(elemType)
        }

      case OperEx(TlaFunOper.enum, kv@_*) =>
        val keys = kv.zipWithIndex.filter(_._2 % 2 == 0).map(_._1) // pick the even indices (starting with 0)
      def toStr(key: TlaEx) = key match {
        case ValEx(TlaStr(s)) => s
        case _ => throw new RewriterException("Expected a string, found: %s".format(key))
      }

        val vals = kv.zipWithIndex.filter(_._2 % 2 == 1).map(_._1) // pick the odd indices (starting with 0)
      val types = vals map parse
        RecordT(SortedMap(keys.map(toStr).zip(types): _*))

      case OperEx(TlaFunOper.tuple, args@_*) =>
        val types = args map parse
        TupleT(types)

      case e =>
        throw new RewriterException("Unexpected type annotation: %s".format(annot))
    }
  }
}
