package at.forsyte.apalache.tla

import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}

import scala.collection.immutable.HashMap

package object bmcmt {

  /**
   * A theory used to evaluate a TLA+ expression: cells, Booleans, and integers.
   *
   * This concept is obsolete and will be removed in the future.
   * See the <a href="https://github.com/informalsystems/apalache/issues/22">issue</a>.
   */
  sealed abstract class Theory {

    /**
     * Check whether a constant is named after the theory naming convention.
     *
     * @param name a constant name
     * @return if the name follows the naming conventions of this theory.
     */
    def hasConst(name: String): Boolean

    /**
     * Check whether a TLA expression is NameEx(name) and hasConst(name) holds true.
     * @param tlaEx a TLA expression
     * @return true, if tlaEx is NameEx(name) and name is a name of a theory constant.
     */
    def hasNameEx(tlaEx: TlaEx): Boolean = {
      tlaEx match {
        case NameEx(name) if hasConst(name) => true
        case _                              => false
      }
    }

    /**
     * Check, whether a TLA expression is NameEx and a theory constant.
     * If so, return its name.
     *
     * @param tlaEx a TLA expression
     * @return constant name
     * @throws InvalidTlaExException if the expression is not a theory constant
     */
    def nameExToString(tlaEx: TlaEx): String = {
      tlaEx match {
        case NameEx(name) if hasConst(name) =>
          name

        case _ =>
          throw new CheckerException("Expected a cell, found: %s".format(tlaEx), tlaEx)
      }
    }
  }

  case class CellTheory() extends Theory {

    /**
     * The prefix of all cells.
     */
    val namePrefix = "$C$"

    /**
     * Check whether a constant is named after the theory naming convention.
     *
     * @param name a constant name
     * @return if the name follows the naming conventions of this theory.
     */
    override def hasConst(name: String): Boolean = {
      name.startsWith(namePrefix)
    }

    override def toString: String = "Cell"
  }
}
