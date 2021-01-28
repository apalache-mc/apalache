package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.tla.bmcmt.profiler.SmtListener
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell, StackableContext}
import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A context that stores the SMT constraints that are generated in the course of symbolic exploration.
  *
  * @author Igor Konnov
  */
trait SolverContext extends StackableContext {

  /**
    * Configuration parameters.
    */
  val config: SolverConfig

  /**
    * Declare a constant for an arena cell.
    * This method is called automatically by the arena.
    *
    * @param cell a (previously undeclared) cell
    */
  def declareCell(cell: ArenaCell): Unit

  /**
    * Declare an arena edge of type 'has'. This method introduces a Boolean variable for the edge.
    * This method is called automatically by the arena. If the context already contains the constant
    * with the same name, then this method does nothing.
    *
    * @param set the containing set
    * @param elem a set element
    */
  def declareInPredIfNeeded(set: ArenaCell, elem: ArenaCell): Unit

  /**
    * Check whether the current view of the SMT solver is consistent with arena.
    * @param arena an arena
    */
  def checkConsistency(arena: Arena): Unit

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
    * Check satisfiability of the context with a timeout
    *
    * @param timeoutSec the timeout in seconds. If timeout <= 0, it is not effective
    * @return Some(result), if no timeout happened; otherwise, None
    */
  def satOrTimeout(timeoutSec: Long): Option[Boolean]

  /**
    * Register an SMT listener
    *
    * @param listener register a listener, overrides the previous listener, if it was set before
    */
  def setSmtListener(listener: SmtListener): Unit

  /**
    * Get the current metrics in the solver context. The metrics may change when the other methods are called.
    * @return the current metrics
    */
  def metrics(): SolverContextMetrics
}
