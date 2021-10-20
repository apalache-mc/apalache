package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * An abstract test suite that is parameterized by the snapshot type.
 *
 * @author Igor Konnov
 */
trait TestFilteredTransitionExecutor[SnapshotT] extends ExecutorBase[SnapshotT] {
  test("filtered check enabled and discard") { exeCtx: ExecutorContextT =>
    // x' <- 1 /\ y' <- 1
    val init = tla.and(mkAssign("y", 1), mkAssign("x", 1))
    // x' <- x /\ y' <- x + y
    val next1 = tla.and(mkAssign("x", tla.name("x")), mkAssign("y", tla.plus(tla.name("x"), tla.name("y"))))
    val next2 = tla.and(
        mkAssign("x", tla.name("y")),
        mkAssign("y", tla.name("x"))
    ) ///
    // check the transitions
    val impl = new TransitionExecutorImpl(Set.empty, Set("x", "y"), exeCtx)
    impl.debug = true
    val transFilter = "(0->.*|1->2|2->1)"
    val invFilter = ""
    val trex = new FilteredTransitionExecutor[SnapshotT](transFilter, invFilter, impl)
    // Init
    val isTranslated0 = trex.prepareTransition(3, init)
    assert(isTranslated0)
    trex.pickTransition()
    trex.nextState()
    // Next
    val isTranslated11 = trex.prepareTransition(1, next1)
    assert(!isTranslated11)
    val isTranslated12 = trex.prepareTransition(2, next2)
    assert(isTranslated12)
    trex.pickTransition()
    trex.nextState()
    // Next
    val isTranslated21 = trex.prepareTransition(1, next1)
    assert(isTranslated21)
    val isTranslated22 = trex.prepareTransition(2, next2)
    assert(!isTranslated22)
  }

  test("filtered mayChangeAssertion") { exeCtx: ExecutorContextT =>
    // x' <- 1 /\ y' <- 1
    val init = tla.and(mkAssign("y", 1), mkAssign("x", 1))
    // x' <- x /\ y' <- x + y
    val nextTrans = tla.and(mkAssign("x", tla.name("x")), mkAssign("y", tla.plus(tla.name("x"), tla.name("y"))))
    // push Init
    val impl = new TransitionExecutorImpl(Set.empty, Set("x", "y"), exeCtx)
    impl.debug = true
    val transFilter = ""
    val invFilter = "(0|2)"
    val trex = new FilteredTransitionExecutor[SnapshotT](transFilter, invFilter, impl)
    trex.prepareTransition(1, init)
    trex.pickTransition()
    trex.nextState()
    // prepare Next
    trex.prepareTransition(1, nextTrans)
    // check what has changed + what is filtered
    val inv1 = tla.ge(tla.name("x"), tla.int(3))
    val mayChange1 = trex.mayChangeAssertion(1, inv1)
    assert(!mayChange1)
    val inv2 = tla.ge(tla.name("y"), tla.name("x"))
    val mayChange2 = trex.mayChangeAssertion(1, inv2)
    assert(!mayChange2)
    trex.pickTransition()
    trex.nextState()
    // prepare Next
    trex.prepareTransition(1, nextTrans)
    // everything could have changed as the invariant filter was applied in the previous step
    val mayChange21 = trex.mayChangeAssertion(1, inv1)
    assert(mayChange21)
    val mayChange22 = trex.mayChangeAssertion(1, inv2)
    assert(mayChange22)
  }

  test("filtered regression on #108") { exeCtx: ExecutorContextT =>
    // y' <- 1
    val init = tla.and(mkAssign("y", 1))
    // y' <- y + 1
    val nextTrans = mkAssign("y", tla.plus(tla.name("y"), tla.int(1)))
    // push Init
    val invFilter = "(1|2)"
    val impl = new TransitionExecutorImpl(Set.empty, Set("y"), exeCtx)
    val trex = new FilteredTransitionExecutor[SnapshotT]("", invFilter, impl)
    trex.prepareTransition(1, init)
    trex.pickTransition()
    // the user told us not to check the invariant in state 0
    val notInv = tla.bool(false)
    val mayChange1 = trex.mayChangeAssertion(1, notInv)
    assert(!mayChange1)
    trex.nextState()
    // apply Next
    trex.prepareTransition(1, nextTrans)
    // we must check the invariant right now, as it was skipped earlier
    val mayChange2 = trex.mayChangeAssertion(1, notInv)
    assert(mayChange2)
    trex.pickTransition()
    trex.nextState()
    // apply Next
    trex.prepareTransition(1, nextTrans)
    // this time we should skip the check
    val mayChange3 = trex.mayChangeAssertion(1, notInv)
    assert(!mayChange3)
  }

  private def mkAssign(name: String, value: Int) =
    tla.assignPrime(tla.name(name), tla.int(value))

  private def mkAssign(name: String, rhs: TlaEx) =
    tla.assignPrime(tla.name(name), rhs)
}
