package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.rules.aux.Oracle
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{BoolT1, NameEx, OperEx, TlaEx, Typed}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed

/**
 * ConstrainedTransitionExecutor allows us to add path constraints at certain depths.
 *
 * @param trex transition executor to decorate
 * @tparam ExecutorContext executor context
 * @author Igor Konnov
 */
class ConstrainedTransitionExecutor[ExecutorContext](trex: TransitionExecutor[ExecutorContext])
    extends TransitionExecutor[ExecutorContext] {
  type PathConstraint = List[TlaEx]

  // path constraints per path length
  private var pathConstraints: Map[Int, List[PathConstraint]] = Map.empty

  /**
   * Add a path constraint that is applied, whenever a symbolic execution is extended to the length of the path constraint.
   * This constraint is translated into a disjunction of constraints over individual states.
   *
   * @param constraint path constraint
   */
  def addPathOrConstraint(constraint: PathConstraint): Unit = {
    val len = constraint.length
    pathConstraints += len -> (constraint :: pathConstraints.getOrElse(constraint.length, Nil))

    assertPathOrConstraint(trex.execution, constraint)
  }

  /**
   * Push path constraints immediately in the context.
   */
  def assertPathConstraints(): Unit = {
    val exec = trex.execution
    pathConstraints.get(exec.path.length).foreach {
      _.foreach { cons =>
        assertPathOrConstraint(exec, cons)
      }
    }
  }

  override def assumeTransition(transitionNo: Int): Unit = {
    trex.assumeTransition(transitionNo)
    assertPathConstraints()
  }

  override def pickTransition(): Oracle = {
    val oracle = trex.pickTransition()
    assertPathConstraints()
    oracle
  }

  private def assertPathOrConstraint(execution: EncodedExecution, pathConstraint: PathConstraint): Unit = {
    if (execution.path.length >= pathConstraint.length) {
      val constraints =
        execution.path.tail.zip(pathConstraint.tail).map { case ((binding, _), cons) =>
          // substitute variable names with the cells in the binding
          binding.toMap.foldLeft(cons) { case (ex, (varName, cell)) =>
            val repl = ReplaceFixed(new IdleTracker())

            def isToReplace: TlaEx => Boolean = {
              case NameEx(name) => name == varName
              case _            => false
            }

            val tt = cell.cellType.toTlaType1
            repl(isToReplace, cell.toNameEx.withTag(Typed(tt)))(ex)
          }
        }

      // assert that one of the constraints along the path holds true
      trex.assertState(OperEx(TlaBoolOper.or, constraints: _*)(Typed(BoolT1())))
    }
  }

  //////////////////////////// delegate to trex

  override def stepNo: Int = trex.stepNo

  override def execution: EncodedExecution = trex.execution

  override def initializeConstants(constInit: TlaEx): Unit = trex.initializeConstants(constInit)

  override def prepareTransition(transitionNo: Int, transitionEx: TlaEx): Boolean =
    trex.prepareTransition(transitionNo, transitionEx)

  override def preparedTransitionNumbers: Set[Int] = trex.preparedTransitionNumbers

  override def nextState(): Unit = trex.nextState()

  override def mayChangeAssertion(transitionNo: Int, assertion: TlaEx): Boolean =
    trex.mayChangeAssertion(transitionNo, assertion)

  override def assertState(assertion: TlaEx): Unit = trex.assertState(assertion)

  override def sat(timeoutSec: Long): Option[Boolean] = trex.sat(timeoutSec)

  override def decodedExecution(): DecodedExecution = trex.decodedExecution()

  override def dispose(): Unit = trex.dispose()

  override def snapshot(): ExecutionSnapshot[ExecutorContext] = trex.snapshot()

  override def recover(shot: ExecutionSnapshot[ExecutorContext]): Unit = trex.recover(shot)
}
