package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{BoolT, IntT}
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Coercion from one theory to another.
  *
  * @author Igor Konnov
  */
class Coercion(val stateRewriter: SymbStateRewriter) {
  def coerce(state: SymbState, targetTheory: Theory): SymbState = {
    // if the expression is a constant, find its theory
    val exTheory =
      if (BoolTheory().hasNameEx(state.ex)) {
        BoolTheory()
      } else if (IntTheory().hasNameEx(state.ex)) {
        IntTheory()
      } else if (CellTheory().hasNameEx(state.ex)) {
        CellTheory()
      } else {
        state.theory // not a constant, assume the state theory
      }

    if (targetTheory == exTheory) {
      // nothing to do
      state.setTheory(targetTheory)
    } else {
      (exTheory, targetTheory) match {
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
        if (name == state.solverCtx.falseConst) {
          // $B$0 -> $C$0
          state.setRex(state.arena.cellFalse().toNameEx)
            .setTheory(CellTheory())
        } else if (name == state.solverCtx.trueConst) {
          // $B$1 -> $C$1
          state.setRex(state.arena.cellTrue().toNameEx)
            .setTheory(CellTheory())
        } else {
          // the general case
          val newArena = state.arena.appendCell(BoolT())
          val newCell = newArena.topCell
          val equiv = OperEx(TlaBoolOper.equiv,
            NameEx(name),
            OperEx(TlaOper.eq, newCell.toNameEx, newArena.cellTrue().toNameEx))
          state.solverCtx.assertGroundExpr(equiv)
          state.setArena(newArena)
            .setRex(newCell.toNameEx)
            .setTheory(CellTheory())
        }

      case _ =>
        throw new InvalidTlaExException("Expected a Boolean predicate, found: " + state.ex, state.ex)
    }
  }

  private def cellToBool(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(name) if CellTheory().hasConst(name) =>
        if (name == state.arena.cellFalse().toString) {
          // $C$0 -> $B$0
          state.setRex(NameEx(state.solverCtx.falseConst))
            .setTheory(BoolTheory())
        } else if (name == state.arena.cellTrue().toString) {
          // $C$1 -> $B$1
          state.setRex(NameEx(state.solverCtx.trueConst))
            .setTheory(BoolTheory())
        } else {
          // general case
          val pred = state.solverCtx.introBoolConst()
          val equiv = OperEx(TlaBoolOper.equiv,
            NameEx(pred),
            OperEx(TlaOper.eq, NameEx(name), state.arena.cellTrue().toNameEx))
          state.solverCtx.assertGroundExpr(equiv)
          state.setRex(NameEx(pred))
            .setTheory(BoolTheory())
        }

      case _ =>
        throw new InvalidTlaExException("Expected a cell, found: " + state.ex, state.ex)
    }
  }

  private def intToCell(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(name) if IntTheory().hasConst(name) =>
        val newArena = state.arena.appendCell(IntT())
        val newCell = newArena.topCell
        val equiv = OperEx(TlaOper.eq, NameEx(name), newCell.toNameEx)
        state.solverCtx.assertGroundExpr(equiv)
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
        state.solverCtx.assertGroundExpr(equiv)
        state.setRex(NameEx(intConst))
          .setTheory(IntTheory())

      case _ =>
        throw new InvalidTlaExException("Expected an integer predicate, found: " + state.ex, state.ex)
    }
  }
}
