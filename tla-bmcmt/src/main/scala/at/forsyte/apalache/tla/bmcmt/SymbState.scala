package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A state of symbolic execution.
  *
  * @author Igor Konnov
  */
class SymbState(val ex: TlaEx,
                val arena: Arena,
                val binding: Binding,
                val solverCtx: SolverContext) {

  def setRex(nex: TlaEx): SymbState = {
    new SymbState(nex, arena, binding, solverCtx)
  }

  def setArena(newArena: Arena): SymbState = {
    new SymbState(ex, newArena, binding, solverCtx)
  }

  def setBinding(newBinding: Binding): SymbState = {
    new SymbState(ex, arena, newBinding, solverCtx)
  }

  def setSolverCtx(context: SolverContext): SymbState = {
    new SymbState(ex, arena, binding, context)
  }
}
