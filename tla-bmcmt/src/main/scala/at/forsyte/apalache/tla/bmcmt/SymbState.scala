package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A state of symbolic execution.
  *
  * @author Igor Konnov
  */
class SymbState(val ex: TlaEx,
                val theory: Theory,
                val arena: Arena,
                val binding: Binding,
                val solverCtx: SolverContext) {

  def setRex(nex: TlaEx): SymbState = {
    new SymbState(nex, theory, arena, binding, solverCtx)
  }

  def setTheory(newTheory: Theory): SymbState = {
    new SymbState(ex, newTheory, arena, binding, solverCtx)
  }

  def setArena(newArena: Arena): SymbState = {
    new SymbState(ex, theory, newArena, binding, solverCtx)
  }

  def setBinding(newBinding: Binding): SymbState = {
    new SymbState(ex, theory, arena, newBinding, solverCtx)
  }

  def setSolverCtx(context: SolverContext): SymbState = {
    new SymbState(ex, theory, arena, binding, context)
  }
}
