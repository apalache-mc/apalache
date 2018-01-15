package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.FinSetT
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaOper, TlaSetOper}

/**
  * Implements the rule: SE-UNION, that is, a union of all set elements.
  *
  * @author Igor Konnov
  */
class SetUnionRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.union, set) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.union, topSet) =>
        // rewrite the arguments into memory cells
        val newState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(topSet))
        val topSetCell = newState.arena.findCellByNameEx(newState.ex)
        val elemType =
          topSetCell.cellType match {
            case FinSetT(FinSetT(et)) => et
            case _ => throw new TypeException(s"Applying UNION to $topSet of type ${topSetCell.cellType}" )
          }

        var arena = newState.arena
        val sets = Set(arena.getHas(topSetCell) :_*).toList // remove duplicates too
        // use sets to immediately find repetitive cells
        val allElems = sets.foldLeft(Set[ArenaCell]()) ((all, s) => Set(arena.getHas(s) :_*).union(all))
        // introduce a set cell
        arena = arena.appendCell(FinSetT(elemType))
        val newSetCell = arena.topCell

        if (allElems.isEmpty) {
          // just return an empty set
          // TODO: cache empty sets!
          val finalState = newState.setRex(newSetCell).setArena(arena)
          rewriter.coerce(finalState, state.theory) // coerce to the source theory
        } else {
          // add all the elements to the arena
          arena = allElems.foldLeft(arena) ((a, c) => a.appendHas(newSetCell, c))

          // require each cell to be in one of the sets
          def addCellCons(elemCell: ArenaCell): Unit = {
            val inUnionSet = tla.in(elemCell, newSetCell)
            val existsSet = tla.or(sets.map(s => tla.and(tla.in(s, topSetCell), tla.in(elemCell, s))) :_*)
            val iff = OperEx(TlaOper.eq, inUnionSet, existsSet)
            rewriter.solverContext.assertGroundExpr(iff)
          }

          // add SMT constraints
          for (elem <- allElems)
            addCellCons(elem)

          // that's it
          val finalState = newState.setArena(arena).setRex(newSetCell.toNameEx)
          rewriter.coerce(finalState, state.theory) // coerce to the source theory
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
