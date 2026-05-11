package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.profiler.SmtListener
import at.forsyte.apalache.tla.lir.TlaEx
import com.typesafe.scalalogging.LazyLogging
import io.github.cvc5.Solver
import io.github.cvc5.TermManager

/**
 * A cvc5-backed implementation of [[SolverContext]].
 *
 * This class is intentionally a skeleton while the cvc5 term translation is implemented. It wires the backend into
 * Apalache's solver-selection path and centralizes cvc5 option handling, but solver operations still fail explicitly.
 */
class Cvc5SolverContext(val config: SolverConfig) extends SolverContext with LazyLogging {
  private val termManager = new TermManager()
  private val solver = new Solver(termManager)
  private var level: Int = 0

  solver.setOption("produce-models", "true")
  config.cvc5Params.foreach { case (k, v) =>
    solver.setOption(k, v.toString)
  }

  override def contextLevel: Int = level

  override def push(): Unit = {
    solver.push()
    level += 1
  }

  override def pop(): Unit = {
    pop(1)
  }

  override def pop(n: Int): Unit = {
    require(n >= 0, s"Expected a non-negative number of contexts to pop, found $n.")
    if (n > 0) {
      solver.pop(n)
      level -= n
    }
  }

  override def dispose(): Unit = {
    solver.deletePointer()
    termManager.deletePointer()
  }

  override def declareCell(cell: ArenaCell): Unit = notImplemented()

  override def declareInPredIfNeeded(set: ArenaCell, elem: ArenaCell): Unit = notImplemented()

  override def checkConsistency(arena: PureArenaAdapter): Unit = notImplemented()

  override def assertGroundExpr(ex: TlaEx): Unit = notImplemented()

  override def evalGroundExpr(ex: TlaEx): TlaEx = notImplemented()

  override def log(message: => String): Unit = {
    if (config.debug) {
      logger.debug(message)
    }
  }

  override def sat(): Boolean = notImplemented()

  override def satOrTimeout(timeoutSec: Int): Option[Boolean] = notImplemented()

  override def setSmtListener(listener: SmtListener): Unit = ()

  override def metrics(): SolverContextMetrics = SolverContextMetrics.empty

  private def notImplemented[A](): A = {
    throw new UnsupportedOperationException("The cvc5 solver backend is not implemented yet.")
  }
}
