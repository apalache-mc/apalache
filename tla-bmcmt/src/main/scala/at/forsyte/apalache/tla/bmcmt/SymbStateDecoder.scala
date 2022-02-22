package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.rules.aux.ProtoSeqOps
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.UntypedPredefs.BuilderExAsUntyped
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.convenience.tla.fromTlaEx
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.typecheck.ModelValueHandler
import com.typesafe.scalalogging.LazyLogging

import java.io.PrintWriter
import scala.collection.immutable.{HashSet, SortedSet}

/**
 * This class dumps relevant values from an SMT model using an arena.
 *
 * @author
 *   Igor Konnov
 */
class SymbStateDecoder(solverContext: SolverContext, rewriter: SymbStateRewriter) extends LazyLogging {
  private val protoSeqOps = new ProtoSeqOps(rewriter)

  def decodeStateVariables(state: SymbState): Map[String, TlaEx] = {
    state.binding.toMap.map(p => (p._1, reverseMapVar(decodeCellToTlaEx(state.arena, p._2), p._1, p._2)))
  }

  def decodeCellToTlaEx(arena: Arena, cell: ArenaCell): TlaEx = cell.cellType match {
    case BoolT() =>
      solverContext.evalGroundExpr(cell.toNameEx).withTag(Typed(BoolT1()))

    case IntT() =>
      solverContext.evalGroundExpr(cell.toNameEx).withTag(Typed(IntT1()))

    case ConstT(_) =>
      // First, attempt to check the cache
      val found = rewriter.modelValueCache.findKey(cell)
      if (found.isDefined) {
        val pa @ (utype, index) = found.get
        if (utype == ModelValueHandler.STRING_TYPE)
          tla.str(index).typed()
        else
          tla.str(ModelValueHandler.construct(pa)).typed()
      } else {
        // if not in the cache, it might be the case that another cell, which has asserted equivalence
        // with the original cell can be found
        findCellInSet(arena, rewriter.modelValueCache.values().toSeq, cell.toNameEx) match {
          // found among the cached keys
          case Some(c) =>
            decodeCellToTlaEx(arena, c)

          case None =>
            // not found, just use the name
            // a value that was assigned by the solver, and not created by us
            tla.str(cell.toString).typed()
        }
      }

    case UnknownT() =>
      throw new IllegalStateException(s"Found cell $cell of cell type Unknown")

    case setT @ FinSetT(elemT) =>
      val setT1 = setT.toTlaType1

      def inSet(e: ArenaCell) = {
        val mem = tla
          .apalacheSelectInSet(fromTlaEx(e.toNameEx).typed(elemT.toTlaType1),
              fromTlaEx(cell.toNameEx).typed(setT.toTlaType1))
          .typed(BoolT1())
        solverContext.evalGroundExpr(mem) == tla.bool(true).typed()
      }

      val elems = arena.getHas(cell).filter(inSet)
      val decodedElems = elems.map(decodeCellToTlaEx(arena, _))
      // try to normalize the set for better user experience
      val niceElems = decodedElems.distinct.sortWith(SymbStateDecoder.compareTlaExByStr)
      tla
        .enumSet(niceElems: _*)
        .typed(setT1)

    case ffsT @ FinFunSetT(_, _) =>
      val fromSet = decodeCellToTlaEx(arena, arena.getDom(cell))
      val toSet = decodeCellToTlaEx(arena, arena.getCdm(cell))
      tla
        .funSet(fromSet, toSet)
        .typed(ffsT.toTlaType1)

    case funT @ FunT(_, _) =>
      val funT1 = funT.toTlaType1.asInstanceOf[FunT1]

      // a function is represented with the relation {(x, f[x]) : x \in S}
      val relation = arena.getCdm(cell)

      def isInRelation(pair: ArenaCell): Boolean = {
        val mem =
          tla.apalacheSelectInSet(pair.toNameEx as funT1.arg,
              relation.toNameEx as TupT1(funT1.arg, funT1.res)) as BoolT1()
        solverContext.evalGroundExpr(mem) == tla.bool(true).typed(BoolT1())
      }

      def decodePair(seen: Map[TlaEx, TlaEx], pair: ArenaCell): Map[TlaEx, TlaEx] = {
        val keyCell :: valueCell :: _ = arena.getHas(pair)
        val keyEx = decodeCellToTlaEx(arena, keyCell)
        if (seen.contains(keyEx)) {
          seen
        } else {
          val valueEx = decodeCellToTlaEx(arena, valueCell)
          seen + (keyEx -> valueEx)
        }
      }

      val pairT = TupT1(funT1.arg, funT1.res)
      val pairs = arena
        .getHas(relation)
        .filter(isInRelation)
        .foldLeft(Map[TlaEx, TlaEx]())(decodePair)
        .map(p => tla.tuple(p._1, p._2) as pairT)
        .toSeq
      tla.apalacheSetAsFun(tla.enumSet(pairs: _*) as SetT1(pairT)) as funT1

    case SeqT(elemT) =>
      val elemT1 = elemT.toTlaType1
      val (protoSeq, lenCell, capacity) = protoSeqOps.unpackSeq(arena, cell)
      val len = decodeCellToTlaEx(arena, lenCell) match {
        case ValEx(TlaInt(n)) =>
          // if the length value is corrupt, adjust it
          if (n < 0 || n > capacity) {
            logger.warn(s"Sequence length should belong to 0..$capacity, found: $n")
            Math.min(Math.max(0, n.toInt), capacity)
          } else {
            n.toInt
          }
      }
      val decodedElems = protoSeqOps.elems(arena, protoSeq).map(decodeCellToTlaEx(arena, _)).toList.slice(0, len)
      tla.tuple(decodedElems: _*).typed(SeqT1(elemT1))

    case r @ RecordT(_) =>
      def exToStr(ex: TlaEx): TlaStr = ex match {
        case ValEx(s @ TlaStr(_)) => s
        case _                    => throw new RewriterException("Expected a string, found: " + ex, ex)
      }

      // Note that the domain may have fewer fields than the record type is saying.
      // This comes from the fact that we can extend a record with a richer type.
      val domCell = arena.getDom(cell)
      val dom = decodeSet(arena, domCell) map exToStr
      val fieldValues = arena.getHas(cell)
      val keyList = r.fields.keySet.toList

      def eachField(es: List[TlaEx], key: String): List[TlaEx] = {
        if (!dom.contains(TlaStr(key))) {
          es // skip
        } else {
          val index = keyList.indexOf(key)
          val valueCell = fieldValues(index)
          tla.str(key).typed() +: decodeCellToTlaEx(arena, valueCell) +: es
        }
      }

      val keysAndValues = keyList.reverse.foldLeft(List[TlaEx]())(eachField)
      if (keysAndValues.nonEmpty) {
        OperEx(TlaFunOper.enum, keysAndValues: _*)(Typed(r.toTlaType1))
      } else {
        logger.error(
            s"Decoder: Found an empty record $cell when decoding a counterexample, domain = $domCell. This is a bug.")
        // for debugging purposes, just return a string
        tla.str(s"Empty record domain $domCell").typed()
      }

    case t @ TupleT(_) =>
      val tupleElems = arena.getHas(cell)
      val elemAsExprs = tupleElems.map(c => decodeCellToTlaEx(arena, c))
      tla.tuple(elemAsExprs: _*).typed(t.toTlaType1)

    case PowSetT(t @ FinSetT(_)) =>
      val baseset = decodeCellToTlaEx(arena, arena.getDom(cell))
      tla.powSet(baseset).typed(SetT1(TlaType1.fromTypeTag(baseset.typeTag)))

    case InfSetT(_) if cell == arena.cellIntSet() =>
      tla.intSet().typed(SetT1(IntT1()))

    case InfSetT(_) if cell == arena.cellNatSet() =>
      tla.natSet().typed(SetT1(IntT1()))

    case _ =>
      throw new RewriterException("Don't know how to decode the cell %s of type %s".format(cell, cell.cellType), NullEx)
  }

  private def decodeSet(arena: Arena, set: ArenaCell): Seq[TlaEx] = {
    decodeCellToTlaEx(arena, set) match {
      case OperEx(TlaSetOper.enumSet, elems @ _*) =>
        elems

      case _ =>
        throw new RewriterException("Unexpected domain structure: " + set, NullEx)
    }
  }

  private def findCellInSet(arena: Arena, cells: Seq[ArenaCell], ex: TlaEx): Option[ArenaCell] = {
    def isEq(c: ArenaCell): Boolean = {
      val query = tla.and(tla.eql(c.toNameEx, ex))
      tla.bool(true).typed() == solverContext.evalGroundExpr(query.untyped())
    }

    cells.find(isEq)
  }

  def reverseMapVar(expr: TlaEx, varName: String, cell: ArenaCell): TlaEx = {
    def rec(ex: TlaEx): TlaEx = ex match {
      case NameEx(name) =>
        if (name != cell.toNameEx.name) {
          ex
        } else {
          NameEx(varName)(ex.typeTag)
        }

      case OperEx(oper, args @ _*) =>
        OperEx(oper, args map rec: _*)(ex.typeTag)

      case _ =>
        ex
    }

    rec(expr)
  }
}

object SymbStateDecoder {
  private def compareTlaExByStr(lhs: TlaEx, rhs: TlaEx): Boolean =
    lhs.toString.compareTo(rhs.toString) <= 0
}
