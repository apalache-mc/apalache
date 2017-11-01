package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}

import scala.collection.immutable.HashMap

package object bmcmt {
  /**
    * Binding variables to memory cells.
    */
  type Binding = HashMap[String, ArenaCell]

  /**
    * Given a name, e.g., as NameEx("name"), test, whether this name corresponds to a cell.
    * @param name variable name
    * @return true iff it is a cell name
    */
  def isCellName(name: String): Boolean = {
    name.startsWith(ArenaCell.namePrefix)
  }

  /**
    * Check, whether a TLA expression is a cell. If so, return its name.
    *
    * @param e a TLA expression
    * @return the cell name
    * @throws InvalidTlaExException if the expression is not a cell
    */
  def cellToString(e: TlaEx): String = {
    e match {
      case NameEx(name) if isCellName(name) =>
          name

      case _ => throw new CheckerException("Expected a cell, found: %s".format(e))
    }
  }
}