package at.forsyte.apalache.tla.bmcmt.types

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.predef.{TlaBoolSet, TlaIntSet, TlaStrSet}
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{NullEx, OperEx, TlaEx, ValEx}

import scala.collection.immutable.SortedMap

/**
  * A parser for type annotations, which are written as TLA+ expressions.
  *
  * @author Igor Konnov
  */
object AnnotationParser {
  /**
    * Parse a TLA+ expression that encodes a type.
    * @param annot a type annotation that is a TLA+ expression.
    * @return a cell type
    */
  def fromTla(annot: TlaEx): CellT = {
    annot match {
      case ValEx(TlaIntSet) =>
        IntT()

      case ValEx(TlaBoolSet) =>
        BoolT()

      case ValEx(TlaStrSet) =>
        ConstT()

      case OperEx(TlaSetOper.enumSet, elemAnnot: TlaEx) =>
        val elemType = fromTla(elemAnnot)
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
        case _ => throw new RewriterException("Expected a string, found: %s".format(key), annot)
      }

        val vals = kv.zipWithIndex.filter(_._2 % 2 == 1).map(_._1) // pick the odd indices (starting with 0)
        val types = vals map fromTla
        RecordT(SortedMap(keys.map(toStr).zip(types): _*))

      case OperEx(TlaFunOper.tuple, args@_*) =>
        val types = args map fromTla
        TupleT(types)

      case OperEx(TlaSetOper.seqSet, elemEx) =>
        val elemType = fromTla(elemEx)
        SeqT(elemType)

      case OperEx(TlaSetOper.funSet, argAnnot: TlaEx, resAnnot: TlaEx) =>
        val argType = fromTla(argAnnot)
        val resType = fromTla(resAnnot)
        FunT(FinSetT(argType), resType)

      case OperEx(TlaSetOper.recSet, args@_* ) =>
        // We know |args| = 0 (mod 2)
        val argPairs = args.grouped( 2 ).toSeq map {
          case Seq( ValEx( TlaStr( s ) ), value ) =>
            (s, fromTla( value ))
          case e => throw new RewriterException("Expected a Seq(string, _) found: %s".format(e), annot)
        }
        RecordT( SortedMap( argPairs : _* ) )

      case e =>
        throw new RewriterException("Unexpected type annotation: %s".format(annot), annot)
    }
  }

  /**
    * Convert a cell type into a TLA+ expression that encodes a respective type annotation.
    * @param tp a cell type
    * @return a TLA+ expression
    */
  def toTla(tp: CellT): TlaEx = {
    tp match {
      case BoolT() => ValEx(TlaBoolSet)
      case IntT() => ValEx(TlaIntSet)
      case ConstT() => ValEx(TlaStrSet)
      case FinSetT(elemT) => tla.enumSet(toTla(elemT))
      case PowSetT(domT) => tla.enumSet(toTla(domT))
      case FunT(domT, resT) => tla.funSet(toTla(domT), tla.enumSet(toTla(resT)))
      case FinFunSetT(domT, cdmType) => tla.enumSet(tla.funSet(toTla(domT), toTla(cdmType)))
      case TupleT(es) => tla.tuple(es map toTla: _*)
      case SeqT(elemT) => tla.seqSet(toTla(elemT))
      case RecordT(fields) =>
        val keys = fields.keys.toSeq
        def fieldOrVal(i: Int) = {
          val k = keys(i / 2)
          if (i % 2 == 0) tla.str(k) else toTla(fields(k))
        }
        val args = 0.until(2 * fields.size) map fieldOrVal
        OperEx(TlaFunOper.enum, args :_*)

      case _ =>
        throw new RewriterException("No translation of type %s to a TLA+ expression".format(tp), NullEx)
    }
  }
}
