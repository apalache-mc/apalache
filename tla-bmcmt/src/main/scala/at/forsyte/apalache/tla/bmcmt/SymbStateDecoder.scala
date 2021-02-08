package at.forsyte.apalache.tla.bmcmt

import java.io.PrintWriter

import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import com.typesafe.scalalogging.LazyLogging

import scala.collection.immutable.{HashSet, SortedSet}

/**
 * This class dumps relevant values from an SMT model using an arena.
 *
 * @author Igor Konnov
 */
class SymbStateDecoder(solverContext: SolverContext, rewriter: SymbStateRewriter) extends LazyLogging {
  // a simple decoder that dumps values into a text file, in the future we need better recovery code
  def dumpArena(state: SymbState, writer: PrintWriter): Unit = {
    val sortedCells = SortedSet[ArenaCell]() ++ state.arena.cellMap.values
    for (c <- sortedCells) {
      writer.println("; %s = %s".format(c, decodeCellToTlaEx(state.arena, c)))
    }

    // compute the equivalence classes for the cells, totally suboptimally
    // TODO: rewrite, I did not think too much at all
    def iseq(c: ArenaCell, d: ArenaCell): Boolean = {
      c.cellType == d.cellType && solverContext.evalGroundExpr(tla.eql(c, d)) == tla.bool(true)
    }

    def merge(cls: List[HashSet[ArenaCell]], c: ArenaCell, d: ArenaCell): List[HashSet[ArenaCell]] = {
      if (!iseq(c, d) || c == d) {
        cls
      } else {
        def pred(s: HashSet[ArenaCell]): Boolean = {
          s.contains(c) || s.contains(d)
        }

        val (two: List[HashSet[ArenaCell]], rest: List[HashSet[ArenaCell]]) = cls.partition(pred)

        def union(x: HashSet[ArenaCell], y: HashSet[ArenaCell]): HashSet[ArenaCell] = {
          x.union(y)
        }

        rest ++ List(two.reduce(union))
      }
    }

    var classes = sortedCells.toList.map(HashSet(_))
    for (c <- sortedCells) {
      for (d <- sortedCells) {
        classes = merge(classes, c, d)
      }
    }
    for (cls <- classes) {
      writer.println("; Equiv. class: {%s}".format(cls.mkString(", ")))
    }
  }

  def decodeStateVariables(state: SymbState): Map[String, TlaEx] = {
    state.binding.toMap.map(p => (p._1, reverseMapVar(decodeCellToTlaEx(state.arena, p._2), p._1, p._2)))
  }

  def decodeCellToTlaEx(arena: Arena, cell: ArenaCell): TlaEx = cell.cellType match {
    case BoolT() | IntT() | FailPredT() =>
      solverContext.evalGroundExpr(cell.toNameEx)

    case ConstT() =>
      val found = rewriter.strValueCache.findKey(cell)
      if (found.isDefined) {
        ValEx(TlaStr(found.get))
      } else {
        findCellInSet(arena, rewriter.strValueCache.values().toSeq, cell.toNameEx) match {
          // found among the cached keys
          case Some(c) =>
            decodeCellToTlaEx(arena, c)

          case None =>
            // not found, just use the name
            ValEx(TlaStr(cell.toString)) // a value that was assigned by the solver, and not created by us
        }
      }

    case UnknownT() =>
      tla.appFun(NameEx("Unknown"), cell)

    case FinSetT(_) =>
      def inSet(e: ArenaCell) = solverContext.evalGroundExpr(tla.in(e, cell)) == tla.bool(true)

      val elems = arena.getHas(cell).filter(inSet)
      val decodedElems = elems.map(decodeCellToTlaEx(arena, _))
      // try to normalize the set for better user experience
      val niceElems = decodedElems.distinct.sortWith(SymbStateDecoder.compareTlaExByStr)
      tla.enumSet(niceElems: _*)

    case FinFunSetT(_, _) =>
      tla.funSet(decodeCellToTlaEx(arena, arena.getDom(cell)), decodeCellToTlaEx(arena, arena.getCdm(cell)))

    case FunT(_, _) =>
      // in the new implementation, every function is represented with the relation {(x, f[x]) : x \in S}
      val relation = arena.getCdm(cell)
      val args =
        decodeCellToTlaEx(arena, relation) match {
          case OperEx(TlaSetOper.enumSet, elems @ _*) =>
            def untuple(e: TlaEx) = e match {
              case OperEx(TlaFunOper.tuple, pair @ _*) =>
                pair

              case _ => throw new RewriterException("Corrupted function: " + relation, NullEx)
            }

            elems flatMap untuple

          case _ => throw new RewriterException("Corrupted function: " + relation, NullEx)
        }

      tla.atat(args: _*)

    case SeqT(_) =>
      val startEndFun = arena.getHas(cell) map (decodeCellToTlaEx(arena, _))
      startEndFun match {
        case ValEx(TlaInt(start)) :: ValEx(TlaInt(end)) +: cells =>
          // note that start >= 0 and end = Len(S) - start
          def isIn(elem: TlaEx, no: Int): Boolean = no >= start && no < end

          val filtered = cells.zipWithIndex filter (isIn _).tupled map (_._1)
          tla.tuple(filtered: _*) // return a tuple as it is the canonical representation of a sequence

        case _ => throw new RewriterException("Corrupted sequence: " + startEndFun, NullEx)
      }

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
          ValEx(TlaStr(key)) +: decodeCellToTlaEx(arena, valueCell) +: es
        }
      }

      val keysAndValues = keyList.reverse.foldLeft(List[TlaEx]())(eachField)
      if (keysAndValues.nonEmpty) {
        OperEx(TlaFunOper.enum, keysAndValues: _*)
      } else {
        logger.error(
            s"Decoder: Found an empty record $cell when decoding a counterexample, domain = $domCell. This is a bug.")
        // for debugging purposes, just return a string
        ValEx(TlaStr(s"Empty record domain $domCell"))
      }

    case t @ TupleT(_) =>
      val tupleElems = arena.getHas(cell)
      val elemAsExprs = tupleElems.map(c => decodeCellToTlaEx(arena, c))
      tla.tuple(elemAsExprs: _*)

    case PowSetT(t @ FinSetT(_)) =>
      tla.powSet(decodeCellToTlaEx(arena, arena.getDom(cell)))

    case InfSetT(elemT) if cell == arena.cellIntSet() =>
      ValEx(TlaIntSet)

    case InfSetT(elemT) if cell == arena.cellNatSet() =>
      ValEx(TlaNatSet)

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
      ValEx(TlaBool(true)) == solverContext.evalGroundExpr(tla.and(tla.eql(c, ex)))
    }

    cells.find(isEq)
  }

  def reverseMapVar(expr: TlaEx, varName: String, cell: ArenaCell): TlaEx = {
    def rec(ex: TlaEx): TlaEx = ex match {
      case NameEx(name) =>
        if (name != cell.name) ex else NameEx(varName)

      case OperEx(oper, args @ _*) =>
        OperEx(oper, args map rec: _*)

      case _ =>
        ex
    }

    rec(expr)
  }
}

object SymbStateDecoder {
  private def compareTlaExByStr(lhs: TlaEx, rhs: TlaEx): Boolean =
    lhs.toSimpleString.compareTo(rhs.toSimpleString) <= 0
}
