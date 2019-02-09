package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.profiler.SmtListener
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A context that stores the SMT constraints that are generated in the course of symbolic exploration.
  *
  * @author Igor Konnov
  */
trait SolverContext extends StackableContext {
  /**
    * Declare a constant for an arena cell.
    * This method is called automatically by the arena.
    *
    * @param cell a (previously undeclared) cell
    */
  def declareCell(cell: ArenaCell): Unit

  /**
    * Declare an arena edge of type 'has'. This method introduces a Boolean variable for the edge.
    * This method is called automatically by the arena.
    *
    * @param set the containing set
    * @param elem a set element
    */
  def declareInPred(set: ArenaCell, elem: ArenaCell): Unit

  /**
    * Check whether the current view of the SMT solver is consistent with arena.
    * @param arena an arena
    */
  def checkConsistency(arena: Arena): Unit

  /**
    * Introduce a new Boolean constant.
    *
    * WARNING: this method is obsolete and will be removed in the future. Just introduce a cell of type BoolT().
    *
    * @return the name of a new constant
    */
  def introBoolConst(): String

  /**
    * Get the names of the active Boolean constants (not the cells of type BoolT).
    * This method is used for debugging purposes and may be slow.
    *
    * @return a list of Boolean constants that are active in the current context
    */
  def getBoolConsts: Iterable[String]

  /**
    * Get the names of the active integer constants (not the cells of type IntT).
    * This method is used for debugging purposes and may be slow.
    *
    * @return a list of integer constants that are active in the current context
    */
  def getIntConsts: Iterable[String]

  /**
    * Introduce a new integer constant.
    *
    * WARNING: this method is obsolete and will be removed in the future. Just introduce a cell of type IntT().
    *
    * @return the name of a new constant
    */
  def introIntConst(): String

  /**
    * Introduce an uninterpreted function associated with a cell.
    *
    * @param domainType a type of the domain
    * @param resultType a type of the result
    * @return the name of the new function (declared in SMT)
    */
  def declareCellFun(cellName: String, domainType: CellT, resultType: CellT): Unit

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
    * Register an SMT listener
    *
    * @param listener register a listener, overrides the previous listener, if it was set before
    */
  def setSmtListener(listener: SmtListener): Unit
}

object SolverContext {
  /**
    * Get the name of the reserved Boolean constant that is always false
    * (useful to avoid messing with the keywords).
    * @return the name (typically, $B$0)
    */
  val falseConst = "$B$0"

  /**
    * Get the name of the reserved Boolean constant that is always false
    * (useful to avoid messing with the keywords).
    * @return the name (typically, $B$1)
    */
  val trueConst = "$B$1"
}

