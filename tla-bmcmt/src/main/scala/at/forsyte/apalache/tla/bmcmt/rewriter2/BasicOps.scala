package at.forsyte.apalache.tla.bmcmt.rewriter2

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.smt.SmtTools.False
import scalaz._
import scalaz.Scalaz._

/**
 * A collection of common methods for manipulating the internal state
 */
object BasicOps {
  private def safeBind(key: String, value: ArenaCell): RewritingComputation[Unit] = modify { s =>
    s.copy(binding = Binding(s.binding.toMap + (key -> value)))
  }

  // Extends the internal binding with key->value
  def bind(key: String, value: ArenaCell): StateCompWithExceptions[Unit] =
    EitherT.rightT(safeBind(key, value))

  private def safeAssertGroundExpr(ex: TlaEx): RewritingComputation[Unit] = modify { s =>
    // xform ex into BoolFormula
    // proof of concept: every formula is False
    s.copy(constraints = False() +: s.constraints)
  }

  // Extends the collection of constraints with the SMT formula represented by ex
  // Note: A real implementation should not use the BoolT1 fragment of TlaEx as a proxy for
  // representing SMT constraints.
  def assertGroundExpr(ex: TlaEx): StateCompWithExceptions[Unit] = EitherT.rightT(safeAssertGroundExpr(ex))

  def safeNewCell(cellType: CellT): RewritingComputation[ArenaCell] = symbState { state =>
    val newArena = state.arena.appendCell(cellType)
    (state.copy(arena = newArena), newArena.topCell)
  }

  // Adds a new cell of the given type to the arena and returns it
  def newCell(cellType: CellT): StateCompWithExceptions[ArenaCell] = EitherT.rightT(safeNewCell(cellType))

  // Shorthand for State[SymbStateInternal, T] { fn }
  def symbState[T](fn: RewritingState => (RewritingState, T)): RewritingComputation[T] =
    State[RewritingState, T] { fn }
}
