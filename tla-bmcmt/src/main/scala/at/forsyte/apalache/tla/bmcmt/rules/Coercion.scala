package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{BoolType, IntType}
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Coercion from one theory to another.
  *
  * @author Igor Konnov
  */
class Coercion(val stateRewriter: SymbStateRewriter) {
  def coerce(state: SymbState, targetTheory: Theory): SymbState = {
    if (targetTheory == state.theory) {
      // nothing to do
      state
    } else {
      (state.theory, targetTheory) match {
        case (CellTheory(), BoolTheory()) =>
          cellToBool(state)

        case (CellTheory(), IntTheory()) =>
          cellToInt(state)

        case (BoolTheory(), CellTheory()) =>
          boolToCell(state)

        case (IntTheory(), CellTheory()) =>
          intToCell(state)

        case _ =>
          throw new RewriterException("Coercion from %s to %s is not allowed".format(state.theory, targetTheory))
      }
    }
  }

  private def boolToCell(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(name) if BoolTheory().hasConst(name) =>
        val newArena = state.arena.appendCell(BoolType())
        val newCell = newArena.topCell
        val equiv = OperEx(TlaBoolOper.equiv,
          NameEx(name),
          OperEx(TlaOper.eq, newCell.toNameEx, newArena.cellTrue().toNameEx))
        state.solverCtx.assertCellExpr(equiv)
        state.setArena(newArena)
          .setRex(newCell.toNameEx)
          .setTheory(CellTheory())

      case _ =>
        throw new InvalidTlaExException("Expected a Boolean predicate, found: " + state.ex, state.ex)
    }
  }

  private def cellToBool(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(name) if CellTheory().hasConst(name) =>
        val pred = state.solverCtx.introBoolConst()
        val equiv = OperEx(TlaBoolOper.equiv,
          NameEx(pred),
          OperEx(TlaOper.eq, NameEx(name), state.arena.cellTrue().toNameEx))
        state.solverCtx.assertCellExpr(equiv)
        state.setRex(NameEx(pred))
          .setTheory(BoolTheory())

      case _ =>
        throw new InvalidTlaExException("Expected a cell, found: " + state.ex, state.ex)
    }
  }

  private def intToCell(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(name) if IntTheory().hasConst(name) =>
        val newArena = state.arena.appendCell(IntType())
        val newCell = newArena.topCell
        val equiv = OperEx(TlaOper.eq, NameEx(name), newCell.toNameEx)
        state.solverCtx.assertCellExpr(equiv)
        state.setArena(newArena)
          .setRex(newCell.toNameEx)
          .setTheory(CellTheory())

      case _ =>
        throw new InvalidTlaExException("Expected an integer predicate, found: " + state.ex, state.ex)
    }
  }

  private def cellToInt(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(name) if CellTheory().hasConst(name) =>
        val intConst = state.solverCtx.introIntConst()
        val equiv = OperEx(TlaOper.eq, NameEx(name), NameEx(intConst))
        state.solverCtx.assertCellExpr(equiv)
        state.setRex(NameEx(intConst))
          .setTheory(IntTheory())

      case _ =>
        throw new InvalidTlaExException("Expected an integer predicate, found: " + state.ex, state.ex)
    }
  }
}
