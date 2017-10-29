package at.forsyte.apalache.tla.bmcmt

/**
  * A state of symbolic execution.
  *
  * @author Igor Konnov
  */
class SymbState(val rex: Rex,
                val arena: Arena,
                val binding: Binding,
                val solverCtx: SolverContext) {

  def setRex(newRex: Rex) = {
    new SymbState(newRex, arena, binding, solverCtx)
  }

  def setArena(newArena: Arena) = {
    new SymbState(rex, newArena, binding, solverCtx)
  }

  def setBinding(newBinding: Binding) = {
    new SymbState(rex, arena, newBinding, solverCtx)
  }
}
