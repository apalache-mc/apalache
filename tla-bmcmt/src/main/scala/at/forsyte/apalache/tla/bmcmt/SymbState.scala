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
                val binding: Binding) {

  def setRex(nex: TlaEx): SymbState = {
    new SymbState(nex, theory, arena, binding)
  }

  def setTheory(newTheory: Theory): SymbState = {
    new SymbState(ex, newTheory, arena, binding)
  }

  def setArena(newArena: Arena): SymbState = {
    new SymbState(ex, theory, newArena, binding)
  }

  def setBinding(newBinding: Binding): SymbState = {
    new SymbState(ex, theory, arena, newBinding)
  }
}
