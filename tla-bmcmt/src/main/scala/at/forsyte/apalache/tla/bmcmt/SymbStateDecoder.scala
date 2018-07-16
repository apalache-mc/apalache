package at.forsyte.apalache.tla.bmcmt

import java.io.PrintWriter

import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaStr}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

import scala.collection.immutable.{HashSet, SortedSet}

/**
  * This class dumps relevant values from an SMT model using an arena.
  *
  * @author Igor Konnov
  */
class SymbStateDecoder(solverContext: SolverContext, rewriter: SymbStateRewriter) {
  // a simple decoder that dumps values into a text file, in the future we need better recovery code
  def dumpArena(state: SymbState, writer: PrintWriter): Unit = {
    val sortedCells = SortedSet[ArenaCell]() ++ state.arena.cellMap.values
    for (c <- sortedCells) {
      writer.println("%s = %s".format(c, decodeCellToTlaEx(state.arena, c)))
    }

    // compute the equivalence classes for the cells, totally suboptimally
    // TODO: rewrite, I did not think too much at all
    def iseq(c: ArenaCell, d: ArenaCell): Boolean = {
      c.cellType == d.cellType && solverContext.evalGroundExpr(tla.eql(c, d)).identical(tla.bool(true))
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
      writer.println("Equiv. class: {%s}".format(cls.mkString(", ")))
    }

    for (name <- solverContext.getBoolConsts) {
      val value = solverContext.evalGroundExpr(NameEx(name))
      writer.println(s"$name = $value")
    }
  }

  def decodeStateVariables(state: SymbState): Map[String, TlaEx] = {
    state.binding.map(p => (p._1, reverseMapVar(decodeCellToTlaEx(state.arena, p._2), p._1, p._2)))
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
      def inSet(e: ArenaCell) = solverContext.evalGroundExpr(tla.in(e, cell)).identical(tla.bool(true))

      val elems = arena.getHas(cell).filter(inSet)
      tla.enumSet(elems.map(c => decodeCellToTlaEx(arena, c)): _*)

    case FunT(_, _) =>
      val dom = arena.getDom(cell)
      def eachElem(es: List[TlaEx], argCell: ArenaCell): List[TlaEx] = {
        val inSet = solverContext.evalGroundExpr(tla.in(argCell, dom)).identical(tla.bool(true))
        if (inSet) {
          val resultEx = findCellInSet(arena, arena.getHas(arena.getCdm(cell)), tla.appFun(cell, argCell)) match {
            case Some(c) => decodeCellToTlaEx(arena, c) // it may be a set
            case None => solverContext.evalGroundExpr(tla.appFun(cell, argCell)) // fall back
          }
          decodeCellToTlaEx(arena, argCell) +: resultEx +: es
        } else {
          es
        }
      }

      val domElems = arena.getHas(dom)
      // use the same notation as for the records
      val keysAndValues = domElems.reverse.foldLeft(List[TlaEx]()) (eachElem)
      OperEx(TlaFunOper.enum, keysAndValues :_*)

    case r @ RecordT(_) =>
      def exToStr(ex: TlaEx): TlaStr = ex match {
        case ValEx(s @ TlaStr(_)) => s
        case _ => throw new RewriterException("Expected a string, found: " + ex)
      }
      val dom = decodeSet(arena, arena.getDom(cell)) map exToStr
      val tuple = arena.getHas(cell).head
      val tupleElems = arena.getHas(tuple)
      val keyList = r.fields.keySet.toList
      def eachField(es: List[TlaEx], key: TlaStr): List[TlaEx] = {
        val tupleIndex = keyList.indexOf(key.value)
        val valueCell = tupleElems(tupleIndex)
        ValEx(key) +: decodeCellToTlaEx(arena, valueCell) +: es
      }

      val keysAndValues = dom.reverse.toList.foldLeft(List[TlaEx]()) (eachField)
      OperEx(TlaFunOper.enum, keysAndValues :_*)

    case t @ TupleT(_) =>
      val tupleElems = arena.getHas(cell)
      val elemAsExprs  = tupleElems.map(c => decodeCellToTlaEx(arena, c))
      tla.tuple(elemAsExprs :_*)

    case PowSetT(t @ FinSetT(_)) =>
      tla.powSet(decodeCellToTlaEx(arena, arena.getDom(cell)))

    case _ =>
      throw new RewriterException("Don't know how to decode the cell %s of type %s".format(cell, cell.cellType))
  }

  private def decodeSet(arena: Arena, set: ArenaCell): Seq[TlaEx] = {
    decodeCellToTlaEx(arena, set) match {
      case OperEx(TlaSetOper.enumSet, elems@_*) =>
        elems

      case _ =>
        throw new RewriterException("Unexpected domain structure: " + set)
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

      case OperEx(oper, args@_*) =>
        OperEx(oper, args map rec: _*)

      case _ =>
        ex
    }

    rec(expr)
  }
}
