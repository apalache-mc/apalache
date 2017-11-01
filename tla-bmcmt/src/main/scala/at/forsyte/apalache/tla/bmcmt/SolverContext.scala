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
    * Assert that a Boolean TLA+ expression holds true.
    *
    * @param ex a simplified TLA+ expression over cells
    */
  def assertCellExpr(ex: TlaEx): Unit

  /**
    * Is the current context satisfiable?
    *
    * @return true if and only if the context is satisfiable
    */
  def sat(): Boolean
}

