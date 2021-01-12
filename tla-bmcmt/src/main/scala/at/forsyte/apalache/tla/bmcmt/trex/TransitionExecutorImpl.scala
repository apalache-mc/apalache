package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, MockOracle, Oracle, SparseOracle}
import at.forsyte.apalache.tla.bmcmt.util.TlaExUtil
import at.forsyte.apalache.tla.lir.TlaEx
import com.typesafe.scalalogging.LazyLogging

/**
  * <p>A general-purpose symbolic transition executor (or T-Rex).
  * It accumulates the basic logic for executing TLA+
  * transitions, which is used both in the sequential and parallel model checkers.
  * (It could be used to implement predicate abstraction too.)
  * This class is imperative, as taking SMT snapshots and recovering them
  * in the non-incremental case is far from being functional.</p>
  *
  * <p>This class is parameterized by the type of an executor context. Currently, there are two choices:
  * (1) IncrementalExecutorContext and (2) OfflineExecutorContext.</p>
  *
  * @author Igor Konnov
  */
class TransitionExecutorImpl[ExecCtxT](consts: Set[String], vars: Set[String], ctx: ExecutorContext[ExecCtxT])
  extends TransitionExecutor[ExecCtxT] with LazyLogging {

  /**
    * When debug is true, the executor runs additional consistency checks.
    */
  var debug: Boolean = false
  // the current step number
  private var _stepNo: Int = 0

  // the control state of the executor
  private var controlState: ExecutorControlState = Preparing()

  private val initialArena = Arena.create(ctx.rewriter.solverContext)
  // the latest symbolic state that is produced by the rewriter
  var lastState = new SymbState(initialArena.cellTrue().toNameEx, initialArena, Binding())
  // the stack of the variable bindings, one per state, in reverse order, excluding the binding in topState
  private var revStack: List[(Binding, Oracle)] = List((Binding(), new MockOracle(0)))

  // the transitions that are translated with prepareTransition in the current step
  private var preparedTransitions: Map[Int, EncodedTransition] = Map[Int, EncodedTransition]()

  /**
    * The step that is currently encoded.
    */
  override def stepNo: Int = _stepNo

  /**
    * Retrieve the translated symbolic execution
    * @return the accumulated execution
    */
  override def execution: EncodedExecution = EncodedExecution(lastState.arena, revStack.reverse)

  /**
    * Initialize CONSTANTS by applying assignments within a given expression.
    *
    * @param constInit a constant initializer that contains assignments to primed constants.
    */
  override def initializeConstants(constInit: TlaEx): Unit = {
    assert(controlState == Preparing())
    if (_stepNo > 0 || preparedTransitions.nonEmpty) {
      throw new IllegalStateException(s"initializeConstants should be called only against the initial state")
    }
    logger.debug("Initializing CONSTANTS")
    inferTypes(constInit)
    lastState = ctx.rewriter.rewriteUntilDone(lastState.setRex(constInit))
    // check, whether all constants have been assigned
    val shiftedBinding = lastState.binding.shiftBinding(Set.empty)
    if (shiftedBinding.toMap.keySet != consts) {
      val diff = consts -- shiftedBinding.toMap.keySet
      throw new IllegalStateException("CONSTANTS are not initialized: " + diff.mkString(", "))
    }

    shiftTypes(Set.empty) // treat constants as variables

    lastState = lastState.setBinding(shiftedBinding)

    // update the execution stack in place, as we are dealing with the special case of constant initialization
    revStack = List((shiftedBinding, revStack.head._2))
  }

  /**
    * Translate a transition into SMT and save it under the given number. This method returns false,
    * if the transition was found to be disabled during the translation. In this case, the translation result
    * is still saved in the SMT context. It is user's responsibility to pop the context, e.g., by recovering from
    * a snapshot. (In an incremental solver, it is cheap; in an offline solver, this may slow down the checker.)
    *
    * @param transitionNo a number associated with the transition, must be unique for the current step
    * @param transitionEx the expression that encodes the transition, it must be a TLA+ action expression
    * @return true, if the transition has been successfully translated;
    *         false, if the translation has found that the transition is disabled
    */
  override def prepareTransition(transitionNo: Int, transitionEx: TlaEx): Boolean = {
    assert(controlState == Preparing())
    if (preparedTransitions.contains(transitionNo)) {
      throw new IllegalStateException(s"prepareTransition is called for $transitionNo two times")
    }
    logger.debug("Step #%d, transition #%d, SMT context level %d"
      .format(stepNo, transitionNo, ctx.rewriter.contextLevel))
    inferTypes(transitionEx)
    ctx.rewriter.solverContext.log("; ------- STEP: %d, STACK LEVEL: %d TRANSITION: %d {"
      .format(stepNo, ctx.rewriter.contextLevel, transitionNo))
    logger.debug("Translating to SMT...")
    val erased = lastState.setBinding(lastState.binding.forgetPrimed) // forget the previous assignments
    ctx.rewriter.exprCache.disposeActionLevel() // forget the previous action caches
    // translate the transition to SMT
    lastState = ctx.rewriter.rewriteUntilDone(erased.setRex(transitionEx))
    ctx.rewriter.flushStatistics()

    if (debug) {
      // This is a debugging feature that allows us to find incorrect rewriting rules. Disable it in production.
      logger.debug("Checking consistency of the transition constraints")
      if (ctx.solver.sat()) {
        logger.debug("The transition constraints are OK")
      } else {
        // this is a clear sign of a bug in one of the translation rules
        logger.debug("Transition constraints are inconsistent")
        throw new CheckerException("A contradiction introduced in rewriting. Report a bug.", lastState.ex)
      }
    }

    // check, whether all variables have been assigned
    val newBinding = lastState.binding
    lastState = lastState.setBinding(lastState.binding.forgetPrimed) // forget the assignments
    val assignedVars = newBinding.toMap.
      collect { case (name, _) if name.endsWith("'") => name.substring(0, name.length - 1) }
    if (assignedVars.toSet == vars) {
      // the transition can be accessed
      preparedTransitions += transitionNo -> EncodedTransition(lastState.asCell, newBinding)
      true // the transition is probably enabled
    } else {
      logger.debug(s"Transition $transitionNo produces partial assignment. Disabled.")
      false // the transition is disabled
    }
  }

  /**
    * Assume that a previously prepared transition fires. Use this method to check,
    * whether a prepared transition is enabled.
    * This method should be called after prepareTransition.
    *
    * @param transitionNo the number of a previously prepared transition
    */
  override def assumeTransition(transitionNo: Int): Unit = {
    assert(controlState == Preparing())
    // assert that the concerned transition has been prepared
    if (!preparedTransitions.contains(transitionNo)) {
      throw new IllegalStateException(s"Use prepareTransition before calling assumeTransition for $transitionNo")
    } else {
      val transition = preparedTransitions(transitionNo)
      ctx.rewriter.solverContext.assertGroundExpr(transition.trigger.toNameEx)
      lastState = lastState.setBinding(transition.binding)
      // add the binding and the oracle on the stack
      revStack = (lastState.binding.shiftBinding(consts), new MockOracle(transitionNo)) :: revStack
    }

    controlState = Picked()
  }

  /**
    * A syntactic test on whether a translated transition may change satisfiability of an assertion.
    * It tests, whether all variables mentioned in the assertion belong to the unchanged set of the transition.
    *
    * @param transitionNo the index of a previously prepared transition
    * @param assertion    a state expression
    * @return true, if the transition may affect satisfiability of the assertion
    */
  override def mayChangeAssertion(transitionNo: Int, assertion: TlaEx): Boolean = {
    val trans = preparedTransitions(transitionNo)
    val binding = trans.binding

    // copied from SymbState.changed. Remove it from SymbState?
    def addOrSkipVar(set: Set[String], name: String): Set[String] = {
      if (name.endsWith("'")) {
        val nonPrimed = name.substring(0, name.length - 1)
        if (!binding.contains(nonPrimed) || binding(nonPrimed) != binding(name)) {
          set + name
        } else {
          set
        }
      } else {
        set
      }
    }

    val changedPrimes = binding.toMap.keySet.foldLeft(Set[String]())(addOrSkipVar)
    val used = TlaExUtil.findUsedNames(assertion).map(_ + "'")
    // Either the assertion is referring to changed variables,
    // or we are at the initial step, so it's satisfiability may have changed, see #108
    used.intersect(changedPrimes).nonEmpty || _stepNo == 0
  }

  /**
    * Push an assertion about the current controlState.
    *
    * @param assertion a Boolean-valued TLA+ expression, usually a controlState expression,
    *                  though it may be an action expression.
    */
  override def assertState(assertion: TlaEx): Unit = {
    inferTypes(assertion)
    val nextState = ctx.rewriter.rewriteUntilDone(lastState.setRex(assertion))
    ctx.rewriter.solverContext.assertGroundExpr(nextState.ex)
    lastState = nextState.setRex(lastState.ex) // propagate the arena and binding, but keep the old expression
  }

  /**
    * Pick non-deterministically one transition among the transitions that are prepared
    * in the current step. Further, assume that the picked transition has fired.
    * This method must be called after at least one call to prepareTransition.
    */
  override def pickTransition(): Oracle = {
    assert(controlState == Preparing())
    // assert that there is at least one prepared transition
    logger.info("Step %d, level %d: picking a transition out of %d transition(s)"
      .format(stepNo, ctx.rewriter.contextLevel, preparedTransitions.size))
    assert(preparedTransitions.nonEmpty)
    val sortedTransitions = preparedTransitions.toSeq.sortBy(_._1)

    // pick an index j \in { 0..k } of the fired transition
    val picker = new CherryPick(ctx.rewriter)
    val (oracleState, oracle) = picker.oracleFactory.newDefaultOracle(lastState, sortedTransitions.length)

    if (sortedTransitions.isEmpty) {
      throw new IllegalArgumentException("unable to pick transitions from empty set")
    } else if (sortedTransitions.lengthCompare(1) == 0) {
      ctx.solver.assertGroundExpr(sortedTransitions.head._2.trigger.toNameEx)
      lastState = oracleState.setBinding(sortedTransitions.head._2.binding)
      val transitionNo = sortedTransitions.head._1
      // use a fixed transition
      val mockOracle = new MockOracle(transitionNo)
      revStack = (lastState.binding.shiftBinding(consts), mockOracle) :: revStack
    } else {
      // if oracle = i, then the ith transition is enabled
      ctx.solver.assertGroundExpr(oracle.caseAssertions(oracleState, sortedTransitions.map(_._2.trigger.toNameEx)))

      // glue the computed states S_0, ..., S_k together:
      // for every variable x', pick c_x from { S_1[x'], ..., S_k[x'] }
      //   and require \A i \in { 0.. k-1}. j = i => c_x = S_i[x']
      // Then, the final controlState binds x' -> c_x for every x' \in Vars'
      var nextState = oracleState

      def pickVar(x: String): ArenaCell = {
        val toPickFrom = sortedTransitions map (p => p._2.binding(x))
        nextState = picker.pickByOracle(nextState,
          oracle, toPickFrom, nextState.arena.cellFalse().toNameEx) // no else case
        nextState.asCell
      }

      def getAssignedVars(binding: Binding) = binding.forgetNonPrimed(Set()).toMap.keySet
      val primedVars = getAssignedVars(sortedTransitions.head._2.binding) // only VARIABLES, not CONSTANTS

      val finalVarBinding = Binding(primedVars.toSeq map (n => (n, pickVar(n))): _*) // variables only
      val constBinding = Binding(oracleState.binding.toMap.filter(p => consts.contains(p._1)))
      lastState = nextState.setBinding(finalVarBinding ++ constBinding)
      // the sparse oracle is mapping the oracle values to the transition numbers
      val sparseOracle = new SparseOracle(oracle, preparedTransitions.keySet)
      revStack = (lastState.binding.shiftBinding(consts), sparseOracle) :: revStack
      if (debug && !ctx.solver.sat()) {
        throw new InternalCheckerError(s"Error picking next variables (step $stepNo). Report a bug.", lastState.ex)
      }
    }

    controlState = Picked()
    revStack.head._2
  }

  /**
    * Get the numbers of prepared transitions.
    *
    * @return a sequence of numbers
    */
  def preparedTransitionNumbers: Set[Int] = {
    preparedTransitions.keySet
  }

  /**
    * Advance symbolic execution by renaming primed variables to non-primed.
    * This method must be called after pickTransition.
    */
  override def nextState(): Unit = {
    assert(controlState == Picked())
    // finally, shift the primed variables to non-primed, forget the expression
    lastState = lastState
      .setBinding(lastState.binding.shiftBinding(consts))
      .setRex(lastState.arena.cellTrue().toNameEx)
    // save the types of the cells that are bound to the previous variables types,
    // so the transition executor can process assertions over state variables of the whole execution
    vars.map(name => lastState.binding(name))
      .foreach(cell => ctx.typeFinder.extendWithCellType(cell))
    // that is the result of this step
    shiftTypes(consts)
    // importantly, clean the action-level caches, so the new variables are not mapped to the old variables
    ctx.rewriter.exprCache.disposeActionLevel()
    // clean the prepared transitions
    preparedTransitions = Map()
    // increase the step number
    _stepNo += 1
    controlState = Preparing()
  }

  /**
    * Check, whether the current context of the symbolic execution is satisfiable.
    *
    * @param timeoutSec timeout in seconds
    * @return Some(true), if the context is satisfiable;
    *         Some(false), if the context is unsatisfiable;
    *         None, if the solver timed out or reported *unknown*.
    */
  override def sat(timeoutSec: Long): Option[Boolean] = {
    ctx.rewriter.solverContext.satOrTimeout(timeoutSec)
  }

  override def decodedExecution(): DecodedExecution = {
    val decoder = new SymbStateDecoder(ctx.solver, ctx.rewriter)

    def decodePair(binding: Binding, oracle: Oracle): (Map[String, TlaEx], Int) = {
      val transitionNo = oracle.evalPosition(ctx.solver, lastState)
      val decodedState = decoder.decodeStateVariables(lastState.setBinding(binding))
      (decodedState, transitionNo)
    }

    new DecodedExecution(execution.path.map(p => decodePair(p._1, p._2)))
  }

  /**
    * Create a snapshot of the current symbolic execution. The user should not access
    * the snapshot, which is an opaque object.
    *
    * @return a snapshot
    */
  def snapshot(): ExecutorSnapshot[ExecCtxT] = {
    val exe = new EncodedExecution(lastState.arena, ((lastState.binding, new MockOracle(0)) :: revStack).reverse)
    new ExecutorSnapshot[ExecCtxT](controlState, exe, preparedTransitions, ctx.snapshot())
  }

  /**
    * Recover a controlState of symbolic execution from a snapshot.
    *
    * @param snapshot a snapshot that was created by an earlier call to snapshot.
    */
  def recover(snapshot: ExecutorSnapshot[ExecCtxT]): Unit = {
    ctx.recover(snapshot.contextSnapshot)
    val rs = snapshot.execution.path.reverse
    val arena = snapshot.execution.arena.setSolver(ctx.solver)
    lastState = new SymbState(arena.cellTrue().toNameEx, arena, rs.head._1)
    revStack = rs.tail
    preparedTransitions = snapshot.preparedTransitions
    controlState = snapshot.controlState
    // revStack starts with the pre-init state that describes the system before Init has been applied
    // Hence, the step number of the size of the stack, except the pre-init state
    _stepNo = revStack.length - 1
  }

  /**
    * Dispose the transition executor together with its context.
    */
  def dispose(): Unit = {
    ctx.dispose()
  }


  // infer the types and throw an exception if type inference has failed
  private def inferTypes(expr: TlaEx): Unit = {
//    logger.debug("Inferring types...")
    ctx.typeFinder.inferAndSave(expr)
    if (ctx.typeFinder.typeErrors.nonEmpty) {
      throw new TypeInferenceException(ctx.typeFinder.typeErrors)
    }
  }

  /**
    * Remove the non-primed variables (except provided constants)
    * and rename the primed variables to their non-primed versions.
    * After that, remove the type finder to contain the new types only.
    */
  private def shiftTypes(constants: Set[String]): Unit = {
    val types = ctx.typeFinder.varTypes
    // keep the types of prime variables, cells, and constants
    def keep(name: String): Boolean = {
      name.endsWith("'") || ArenaCell.isValidName(name) || constants.contains(name)
    }
    val nextTypes =
      types.filter(p => keep(p._1))
        .map(p => (p._1.stripSuffix("'"), p._2))
    ctx.typeFinder.reset(nextTypes)
  }
}
