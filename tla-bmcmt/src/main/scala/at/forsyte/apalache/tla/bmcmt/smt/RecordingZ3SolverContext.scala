package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.tla.bmcmt.profiler.SmtListener
import at.forsyte.apalache.tla.bmcmt.{Arena, ArenaCell}
import at.forsyte.apalache.tla.lir.TlaEx
import com.typesafe.scalalogging.LazyLogging


object RecordingZ3SolverContext {
  def apply(parentLog: Option[SmtLog], config: SolverConfig): RecordingZ3SolverContext = {
    val context = new RecordingZ3SolverContext(parentLog, config)
    parentLog match {
      case Some(log) =>
        log.replay(context.solver)

      case None => ()
    }
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
class RecordingZ3SolverContext private (parentLog: Option[SmtLog], config: SolverConfig)
    extends SolverContext with Serializable with LazyLogging {

  import SmtLog._

  private val solver = new Z3SolverContext(config)

  /**
    * The sequence of logs (the last added element is in the head),
    * one per context, except the last log, which is maintained in lastLog.
    * Every list in logStackRev is stored in the reverse order.
    */
  private var logStackRev: List[List[Record]] = List()

  /**
    * The current log, the last added element is in the head.
    */
  private var lastLogRev: List[Record] = List()

  def extractLog(): SmtLog = {
    val newRecords = (lastLogRev ++ logStackRev.flatten).reverse
    new SmtLog(parentLog, newRecords)
  }

  /**
    * Get the current context level, that is the difference between the number of pushes and pops made so far.
    *
    * @return the current level, always non-negative.
    */
  override def contextLevel: Int = solver.contextLevel

  /**
    * Save the current context and push it on the stack for a later recovery with pop.
    */
  override def push(): Unit = {
    solver.push()
    logStackRev = lastLogRev :: logStackRev
    lastLogRev = List()
  }

  /**
    * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
    * to save only the latest context.
    */
  override def pop(): Unit = {
    solver.pop()
    lastLogRev = logStackRev.head
    logStackRev = logStackRev.tail
  }

  /**
    * Pop the context as many times as needed to reach a given level.
    *
    * @param n pop n times, if n > 0, otherwise, do nothing
    */
  override def pop(n: Int): Unit = {
    solver.pop(n)
    logStackRev = logStackRev.drop(n - 1) // n - 1 in logStack + 1 in lastLog
    lastLogRev = logStackRev.head
    logStackRev = logStackRev.tail
  }

  /**
    * Clean the context
    */
  override def dispose(): Unit = {
    solver.dispose()
  }

  /**
    * Declare a constant for an arena cell.
    * This method is called automatically by the arena.
    *
    * @param cell a (previously undeclared) cell
    */
  override def declareCell(cell: ArenaCell): Unit = {
    lastLogRev = DeclareCellRecord(cell) :: lastLogRev
    solver.declareCell(cell)
  }

  /**
    * Declare an arena edge of type 'has'. This method introduces a Boolean variable for the edge.
    * This method is called automatically by the arena. If the context already contains the constant
    * with the same name, then this method does nothing.
    *
    * @param set  the containing set
    * @param elem a set element
    */
  override def declareInPredIfNeeded(set: ArenaCell, elem: ArenaCell): Unit = {
    lastLogRev = DeclareInPredRecord(set, elem) :: lastLogRev
    solver.declareInPredIfNeeded(set, elem)
  }

  /**
    * Check whether the current view of the SMT solver is consistent with arena.
    *
    * @param arena an arena
    */
  override def checkConsistency(arena: Arena): Unit = {
    solver.checkConsistency(arena)
  }

  /**
    * Assert that a Boolean TLA+ expression holds true.
    *
    * @param ex a simplified TLA+ expression over cells
    */
  override def assertGroundExpr(ex: TlaEx): Unit = {
    lastLogRev = AssertGroundExprRecord(ex) :: lastLogRev
    solver.assertGroundExpr(ex)
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
    solver.evalGroundExpr(ex)
  }

  /**
    * Write a message to the log file. This is helpful to debug the SMT encoding.
    *
    * @param message message text, call-by-name
    */
  override def log(message: => String): Unit = {
    if (config.debug) {
      solver.log(message)
    }
  }

  /**
    * Is the current context satisfiable?
    *
    * @return true if and only if the context is satisfiable
    */
  override def sat(): Boolean = {
    solver.sat()
  }

  /**
    * Check satisfiability of the context with a timeout
    *
    * @param timeoutSec the timeout in seconds. If timeout <= 0, it is not effective
    * @return Some(result), if no timeout happened; otherwise, None
    */
  override def satOrTimeout(timeoutSec: Long): Option[Boolean] = {
    solver.satOrTimeout(timeoutSec)
  }

  /**
    * Register an SMT listener
    *
    * @param listener register a listener, overrides the previous listener, if it was set before
    */
  override def setSmtListener(listener: SmtListener): Unit = {
    solver.setSmtListener(listener)
  }

  /**
    * Get the current metrics in the solver context. The metrics may change when the other methods are called.
    *
    * @return the current metrics
    */
  override def metrics(): SolverContextMetrics = {
    solver.metrics()
  }
}
