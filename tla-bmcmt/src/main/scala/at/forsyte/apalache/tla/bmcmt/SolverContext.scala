package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A context that stores the SMT constraints that are generated in the course of symbolic exploration.
  *
  * @author Igor Konnov
  */
trait SolverContext extends StackableContext {
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
    * Introduce an uninterpreted function associated with a cell.
    *
    * @param cell an arena cell
    * @return a function declaration (also stored in the context)
    */
  def getOrIntroCellFun(cell: ArenaCell): String

    /**
    * Assert that a Boolean TLA+ expression holds true.
    *
    * @param ex a simplified TLA+ expression over cells
    */
  def assertGroundExpr(ex: TlaEx): Unit

  /**
    * Evaluate a ground TLA+ expression in the current model, which is available after a call to sat().
    * This method assumes that the outcome is either a Boolean or integer.
    * If not, it throws SmtEncodingException.
    *
    * @param ex an expression to evaluate
    * @return a TLA+ value
    */
  def evalGroundExpr(ex: TlaEx): TlaEx

  /**
    * Write a message to the log file. This is helpful to debug the SMT encoding.
    *
    * @param message message text, call-by-name
    */
  def log(message: => String): Unit

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

  /**
    * Get the name of the reserved Boolean constant that should be equal true,
    * whenever a failure occured during an execution
    *
    * @return the name (typically, $B$2)
    */
  def failConst: String
}

