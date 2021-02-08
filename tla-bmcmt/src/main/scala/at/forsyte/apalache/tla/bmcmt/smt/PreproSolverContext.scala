package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.caches.SimpleCache
import at.forsyte.apalache.tla.bmcmt.profiler.SmtListener
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.smt.PreproSolverContext.{PreproEqEntry, PreproInEntry, PreproCacheEntry}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.UntypedPredefs._

object PreproSolverContext {
  sealed abstract class PreproCacheEntry {
    def asTlaEx(negate: Boolean): TlaEx
  }

  case class PreproEqEntry(isEq: Boolean) extends PreproCacheEntry {
    override def asTlaEx(negate: Boolean): TlaEx = tla.bool(if (negate) !isEq else isEq)
  }
  case class PreproInEntry(isIn: Boolean) extends PreproCacheEntry {
    override def asTlaEx(negate: Boolean): TlaEx = tla.bool(if (negate) !isIn else isIn)
  }
}

/**
 * <p>A preprocessor of the SolverContext that caches the following types of constraints and propagates them
 * before pushing the constraints to the actual solver:</p>
 *
 * <ul>
 * <li>Equalities between two cells: tla.eql(c1, c2) and tla.neq(c1, c2)</li>
 * <li>Set membership assertions between two cells: tla.in(c1, c2) and tla.not(tla.in(c1, c2)).
 * </ul>
 *
 * <p>This is helpful as our rewriting rules
 * introduce lots of redundant variables that can be easily eliminated by propagation.
 * We use delegation instead of inheritance, as we will integrate with other solvers in the future.</p>
 *
 * @author Igor Konnov
 */
class PreproSolverContext(context: SolverContext) extends SolverContext {
  private val simplifier = new ConstSimplifierForSmt()
  // FIXME: it would be much better to use cells here, but we do not have access to the arena
  private val cache: SimpleCache[(String, String), PreproCacheEntry] = new SimpleCache()

  /**
   * Configuration parameters.
   */
  override val config: SolverConfig = context.config

  /**
   * Assert that a Boolean TLA+ expression holds true.
   *
   * @param ex a simplified TLA+ expression over cells
   */
  override def assertGroundExpr(ex: TlaEx): Unit = {
    // there are plenty of top-level constraints like (= c1 c2) or tla.in(c1, c2)
    val ppex = simplifier.simplifyShallow(preprocess(simplifier.simplifyShallow(ex)))
    ppex match {
      case OperEx(TlaOper.eq, NameEx(left), NameEx(right)) =>
        // eq and not(ne), the latter is transformed by simplifier
        if (ArenaCell.isValidName(left) && ArenaCell.isValidName(right)) {
          val pair = if (left.compareTo(right) <= 0) (left, right) else (right, left)
          cache.put(pair, PreproEqEntry(true))
          context.log(";;    -> pp eq cached as true ")
        }

      case OperEx(TlaOper.ne, NameEx(left), NameEx(right)) =>
        // ne and not(eq), the latter is transformed by simplifier
        if (ArenaCell.isValidName(left) && ArenaCell.isValidName(right)) {
          val pair = if (left.compareTo(right) <= 0) (left, right) else (right, left)
          cache.put(pair, PreproEqEntry(false))
          context.log(";;    -> pp eq cached as false ")
        }

      case OperEx(TlaSetOper.in, NameEx(left), NameEx(right)) =>
        // in and not(notin), the latter is transformed by simplifier
        if (ArenaCell.isValidName(left) && ArenaCell.isValidName(right)) {
          cache.put((left, right), PreproInEntry(true))
          context.log(";;    -> pp in cached as true ")
        }

      case OperEx(TlaSetOper.notin, NameEx(left), NameEx(right)) =>
        // notin and not(in), the latter is transformed by simplifier
        if (ArenaCell.isValidName(left) && ArenaCell.isValidName(right)) {
          cache.put((left, right), PreproInEntry(false))
          context.log(";;    -> pp in cached as false ")
        }

      case _ => // ignore
    }
    // we have to user assert, as the cells might have been used by earlier constraints
    context.assertGroundExpr(ppex)
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
    context.evalGroundExpr(preprocess(ex))
  }

  private def preprocess(ex: TlaEx): TlaEx = {
    ex match {
      case OperEx(TlaOper.eq, NameEx(left), NameEx(right)) =>
        val pair = if (left.compareTo(right) <= 0) (left, right) else (right, left)
        cache.get(pair) match {
          case Some(cached) => cached.asTlaEx(negate = false)
          case None         => ex
        }

      case OperEx(TlaOper.ne, NameEx(left), NameEx(right)) =>
        val pair = if (left.compareTo(right) <= 0) (left, right) else (right, left)
        cache.get(pair) match {
          case Some(cached) => cached.asTlaEx(negate = true)
          case None         => ex
        }

      case OperEx(TlaSetOper.in, NameEx(left), NameEx(right)) =>
        cache.get((left, right)) match {
          case Some(cached) => cached.asTlaEx(negate = false)
          case None         => ex
        }

      case OperEx(TlaSetOper.notin, NameEx(left), NameEx(right)) =>
        cache.get((left, right)) match {
          case Some(cached) => cached.asTlaEx(negate = true)
          case None         => ex
        }

      case OperEx(TlaSetOper.in, _*) | OperEx(TlaSetOper.notin, _*) =>
        // do not preprocess these expressions, as we have to find sorts from the names
        ex

      case OperEx(TlaFunOper.app, fun, elem) =>
        // Do not preprocess the function, as we have to find sorts from the names.
        // This is not relevant anymore, as we are not using uninterpreted functions.
        OperEx(TlaFunOper.app, fun, preprocess(elem))

      case OperEx(oper, args @ _*) =>
        OperEx(oper, args map preprocess: _*)

      case _ => ex
    }
  }

  ////////////////// the rest is just delegation to context

  /**
   * Declare a constant for an arena cell.
   *
   * @param cell a (previously undeclared) cell
   */
  override def declareCell(cell: ArenaCell): Unit = context.declareCell(cell)

  /**
   * Declare an arena edge of type 'has'. This method introduces a Boolean variable for the edge.
   *
   * @param set  the containing set
   * @param elem a set element
   */
  def declareInPredIfNeeded(set: ArenaCell, elem: ArenaCell): Unit = context.declareInPredIfNeeded(set, elem)

  /**
   * Check whether the current view of the SMT solver is consistent with arena.
   *
   * @param arena an arena
   */
  override def checkConsistency(arena: Arena): Unit = context.checkConsistency(arena)

  /**
   * Write a message to the log file. This is helpful to debug the SMT encoding.
   *
   * @param message message text, call-by-name
   */
  override def log(message: => String): Unit = context.log(message)

  /**
   * Is the current context satisfiable?
   *
   * @return true if and only if the context is satisfiable
   */
  override def sat(): Boolean = context.sat()

  /**
   * Check satisfiability of the context with a timeout
   *
   * @param timeoutSec the timeout in seconds. If timeout <= 0, it is not effective
   * @return Some(result), if no timeout happened; otherwise, None
   */
  override def satOrTimeout(timeoutSec: Long): Option[Boolean] = context.satOrTimeout(timeoutSec)

  /**
   * Register an SMT listener
   *
   * @param listener register a listener, overrides the previous listener, if it was set before
   */
  override def setSmtListener(listener: SmtListener): Unit = context.setSmtListener(listener)

  /**
   * Get the current context level, that is the difference between the number of pushes and pops made so far.
   *
   * @return the current level, always non-negative.
   */
  override def contextLevel: Int = context.contextLevel

  /**
   * Get the current metrics in the solver context. The metrics may change when the other methods are called.
   *
   * @return the current metrics
   */
  override def metrics(): SolverContextMetrics = context.metrics()

  /**
   * Save the current context and push it on the stack for a later recovery with pop.
   */
  override def push(): Unit = {
    context.push()
    cache.push()
  }

  /**
   * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
   * to save only the latest context.
   */
  override def pop(): Unit = {
    cache.pop()
    context.pop()
  }

  /**
   * Pop the context as many times as needed to reach a given level.
   *
   * @param n pop n times, if n > 0, otherwise, do nothing
   */
  override def pop(n: Int): Unit = {
    cache.pop(n)
    context.pop(n)
  }

  /**
   * Clean the context
   */
  override def dispose(): Unit = {
    cache.dispose()
    context.dispose()
  }
}
