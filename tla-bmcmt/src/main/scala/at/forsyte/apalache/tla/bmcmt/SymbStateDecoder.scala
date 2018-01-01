package at.forsyte.apalache.tla.bmcmt

import java.io.PrintWriter

import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

import scala.collection.immutable.{HashSet, SortedSet}

/**
  * This class dumps relevant values from an SMT model using an arena.
  *
  * @author Igor Konnov
  */
class SymbStateDecoder(solverContext: SolverContext) {
  // a simple decoder that dumps values into a text file, in the future we need better recovery code
  def dumpArena(state: SymbState, writer: PrintWriter): Unit = {
    def decode(cell: ArenaCell): TlaEx = {
      cell.cellType match {
        case BoolT() | IntT() =>
          solverContext.evalGroundExpr(cell.toNameEx)

        case FinSetT(_) =>
          def inSet(e: ArenaCell) = solverContext.evalGroundExpr(tla.in(e, cell)).identical(tla.bool(true))
          val elems = state.arena.getHas(cell).filter(inSet).map(_.toNameEx)
          tla.enumSet(elems :_*)

        case FunT(_, _) =>
          def eachElem(e: TlaEx): TlaEx = {
            val funApp = tla.appFun(cell, e)
            val result = solverContext.evalGroundExpr(funApp)
            tla.eql(funApp, result)
          }
          val dom = state.arena.getDom(cell)
          decode(dom) match {
            case OperEx(TlaSetOper.enumSet, elems @ _*) =>
              tla.and(elems.map(eachElem) :_*)

            case _ =>
              throw new RewriterException("Unexpected domain structure: " + dom)
          }

        case UnknownT() =>
          tla.appFun(NameEx("Unknown"), cell)

        case _ =>
          throw new RewriterException("Don't know how to decode the cell %s of type %s".format(cell, cell.cellType))
      }
    }
    val sortedCells = SortedSet[ArenaCell]() ++ state.arena.cellMap.values
    for (c <- sortedCells) {
      writer.println("%s = %s".format(c, decode(c)))
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
  }

  def decodeStateVariables(state: SymbState): Map[String, TlaEx] = {
    state.binding.map(p => (p._1, reverseMapVar(decodeCellToTlaEx(state.arena, p._2), p._1, p._2)))
  }

  def decodeCellToTlaEx(arena: Arena, cell: ArenaCell): TlaEx = cell.cellType match {
    case BoolT() | IntT() =>
      solverContext.evalGroundExpr(cell.toNameEx)

    case FinSetT(_) =>
      def inSet(e: ArenaCell) = solverContext.evalGroundExpr(tla.in(e, cell)).identical(tla.bool(true))
      val elems = arena.getHas(cell).filter(inSet)
      tla.enumSet(elems.map(c => decodeCellToTlaEx(arena, c)) :_*)

    case FunT(_, _) =>
      def eachElem(e: TlaEx): TlaEx = {
        val funApp = tla.appFun(cell, e)
        val result = solverContext.evalGroundExpr(funApp)
        tla.eql(funApp, result)
      }
      val dom = arena.getDom(cell)
      decodeCellToTlaEx(arena, dom) match {
        case OperEx(TlaSetOper.enumSet, elems @ _*) =>
          tla.and(elems.map(eachElem) :_*)

        case _ =>
          throw new RewriterException("Unexpected domain structure: " + dom)
      }

    case UnknownT() =>
      tla.appFun(NameEx("Unknown"), cell)

    case _ =>
      throw new RewriterException("Don't know how to decode the cell %s of type %s".format(cell, cell.cellType))
  }

  def reverseMapVar(expr: TlaEx, varName: String, cell: ArenaCell): TlaEx = {
    def rec(ex: TlaEx): TlaEx = ex match {
      case NameEx(name) =>
        if (name != cell.name) ex else NameEx(varName)

      case OperEx(oper, args @ _*) =>
        OperEx(oper, args map rec :_*)

      case _ =>
        ex
    }

    rec(expr)
  }
}
