package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.tla.bmcmt.profiler.SmtListener
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell}
import at.forsyte.apalache.tla.lir.TlaEx
import com.typesafe.scalalogging.LazyLogging

object RecordingSolverContext {

  /**
    * A factory method to create a recording context on top of a Z3 solver context.
    * The entries in the parent log are replayed right after the start.
    * @param parentLog the parent log for the solver
    * @param config solver config
    * @return a recording solver that works on top of Z3
    */
  def createZ3(
      parentLog: Option[SmtLog],
      config: SolverConfig
  ): RecordingSolverContext = {
    val context =
      new RecordingSolverContext(parentLog, config, new Z3SolverContext(config))
    parentLog.foreach(_.replay(context.solverImpl))
    context
  }
}

/**
  * A wrapper around SolverContext that records SMT operations. The log is organized hierarchically,
  * so a differential diff may be taken.
  *
  * @param parentLog the log of the parent context
  * @param config solver configuration
  *
  * @author Igor Konnov
  */
@SerialVersionUID(700L)
class RecordingSolverContext private (
    parentLog: Option[SmtLog],
    val config: SolverConfig,
    val solverImpl: SolverContext
) extends SolverContext
    with Serializable
    with LazyLogging {

  import SmtLog._

  /**
    * The sequence of logs (the last added element is in the head),
    * one per context. Every element of stackOfInverseLogs is stored in the reverse order.
    */
  private var stackOfInverseLogs: List[List[Record]] = List(List())

  /**
    * Extract a differential SMT log from the current context.
    * @return SMT log
    */
  def extractLog(): SmtLog = {
    val newRecords = stackOfInverseLogs.flatten.reverse
    new SmtLog(parentLog, newRecords)
  }

  /**
    * Get the current context level, that is the difference between the number of pushes and pops made so far.
    *
    * @return the current level, always non-negative.
    */
  override def contextLevel: Int = solverImpl.contextLevel

  /**
    * Save the current context and push it on the stack for a later recovery with pop.
    */
  override def push(): Unit = {
    solverImpl.push()
    stackOfInverseLogs = List() :: stackOfInverseLogs
  }

  /**
    * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
    * to save only the latest context.
    */
  override def pop(): Unit = {
    pop(1)
  }

  /**
    * Pop the context as many times as needed to reach a given level.
    *
    * @param n pop n times, if n > 0, otherwise, do nothing
    */
  override def pop(n: Int): Unit = {
    if (contextLevel - n < 0) {
      throw new IllegalArgumentException(
        s"Trying to pop $n contexts while there are only $contextLevel of them."
      )
    }
    solverImpl.pop(n)
    stackOfInverseLogs = stackOfInverseLogs.drop(n)
  }

  /**
    * Clean the context
    */
  override def dispose(): Unit = {
    solverImpl.dispose()
  }

  /**
    * Declare a constant for an arena cell.
    * This method is called automatically by the arena.
    *
    * @param cell a (previously undeclared) cell
    */
  override def declareCell(cell: ArenaCell): Unit = {
    appendToTopLog(DeclareCellRecord(cell))
    solverImpl.declareCell(cell)
  }

  /**
    * Declare an arena edge of type 'has'. This method introduces a Boolean variable for the edge.
    * This method is called automatically by the arena. If the context already contains a constant
    * with the same name, then this method does nothing.
    *
    * @param set  the containing set
    * @param elem a set element
    */
  override def declareInPredIfNeeded(set: ArenaCell, elem: ArenaCell): Unit = {
    appendToTopLog(DeclareInPredRecord(set, elem))
    solverImpl.declareInPredIfNeeded(set, elem)
  }

  /**
    * Check whether the current view of the SMT solver is consistent with arena.
    *
    * @param arena an arena
    */
  override def checkConsistency(arena: Arena): Unit = {
    solverImpl.checkConsistency(arena)
  }

  /**
    * Assert that a Boolean TLA+ expression holds true.
    *
    * @param ex a simplified TLA+ expression over cells
    */
  override def assertGroundExpr(ex: TlaEx): Unit = {
    appendToTopLog(AssertGroundExprRecord(ex))
    solverImpl.assertGroundExpr(ex)
  }

  /**
    * Evaluate a ground TLA+ expression in the current model, which is available after a call to sat().
    * This method assumes that the outcome is either a Boolean or integer.
    * If not, it throws SmtEncodingException.
    *
    * @param ex an expression to evaluate
    * @return a TLA+ value
    */
  override def evalGroundExpr(ex: TlaEx): TlaEx = {
    solverImpl.evalGroundExpr(ex)
  }

  /**
    * Write a message to the log file. This is helpful to debug the SMT encoding.
    *
    * @param message message text, call-by-name
    */
  override def log(message: => String): Unit = {
    if (config.debug) {
      solverImpl.log(message)
    }
  }

  /**
    * Is the current context satisfiable?
    *
    * @return true if and only if the context is satisfiable
    */
  override def sat(): Boolean = {
    solverImpl.sat()
  }

  /**
    * Check satisfiability of the context with a timeout
    *
    * @param timeoutSec the timeout in seconds. If timeout <= 0, it is not effective
    * @return Some(result), if no timeout happened; otherwise, None
    */
  override def satOrTimeout(timeoutSec: Long): Option[Boolean] = {
    solverImpl.satOrTimeout(timeoutSec)
  }

  /**
    * Register an SMT listener
    *
    * @param listener register a listener, overrides the previous listener, if it was set before
    */
  override def setSmtListener(listener: SmtListener): Unit = {
    solverImpl.setSmtListener(listener)
  }

  /**
    * Get the current metrics in the solver context. The metrics may change when the other methods are called.
    *
    * @return the current metrics
    */
  override def metrics(): SolverContextMetrics = {
    solverImpl.metrics()
  }

  /**
    * Push a record in the topmost log
    * @param rec a record to push
    */
  private def appendToTopLog(rec: Record): Unit = {
    stackOfInverseLogs =
      (rec :: stackOfInverseLogs.head) :: stackOfInverseLogs.tail
  }
}
