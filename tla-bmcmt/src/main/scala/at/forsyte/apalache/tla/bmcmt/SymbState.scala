package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.CellT
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

  /**
    * A convenience function to get the state expression as a cell, if it is actually a cell
   */
  def asCell: ArenaCell = {
    arena.findCellByNameEx(ex)
  }

  /**
    * A convenience function to update arena and save the new arena in a new state.
    */
  def appendArenaCell(cellT: CellT): SymbState = {
    setArena(arena.appendCell(cellT))
  }

  /**
    * Find the names of the variables (their prime versions)
    * that have changed between the primed and non-primed versions.
    *
    * @return the set of names of the variables that have changed, e.g., x', y', and z'
    */
  def changed: Set[String] = {
    def eachName(set: Set[String], name: String): Set[String] = {
      if (name.endsWith("'")) {
        val nonPrimed = name.substring(0, name.length - 1)
        if (!binding.contains(nonPrimed) || binding(nonPrimed) != binding(name)) {
          set + name
        } else {
          set
        }
      } else {
        set
      }
    }

    binding.keySet.foldLeft(Set[String]())(eachName)
  }

}
