package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A context that stores the SMT constraints that are generated in the course of symbolic exploration.
  *
  * @author Igor Konnov
  */
trait SolverContext {
  /**
    * The number of SMT pushes made so far.
    */
  def level: Int

  /**
    * Dispose whatever has to be disposed in the end.
    */
  def dispose()

  /**
    * Push SMT context
    */
  def push(): Unit

  /**
    * Pop SMT context
    */
  def pop(): Unit

  /**
    * Pop back the SMT context until a given level is reached
    * @param level a level to rollback to
    */
  def popTo(level: Int)

  /**
    * Declare a constant for an arena cell.
    *
    * @param cell a (previously undeclared) cell
    */
  def declareCell(cell: ArenaCell): Unit

  /**
    * Introduce a new Boolean constant.
    * @return the name of a new constant
    */
  def introBoolConst(): String

  /**
    * Introduce a new integer constant.
    * @return the name of a new constant
    */
  def introIntConst(): String

  /**
    * Assert that a Boolean TLA+ expression holds true.
    *
    * @param ex a simplified TLA+ expression over cells
    */
  def assertGroundExpr(ex: TlaEx): Unit

  /**
    * Is the current context satisfiable?
    *
    * @return true if and only if the context is satisfiable
    */
  def sat(): Boolean

  /**
    * Get the name of the reserved Boolean constant that is always false
    * (useful to avoid messing with the keywords).
    * @return the name (typically, $B$0)
    */
  def falseConst: String

  /**
    * Get the name of the reserved Boolean constant that is always false
    * (useful to avoid messing with the keywords).
    * @return the name (typically, $B$1)
    */
  def trueConst: String
}

