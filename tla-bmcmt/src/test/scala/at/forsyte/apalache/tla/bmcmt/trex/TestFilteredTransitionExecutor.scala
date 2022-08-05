package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.{ActionInvariant, StateInvariant}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * An abstract test suite that is parameterized by the snapshot type.
 *
 * @author
 *   Igor Konnov
 */
trait TestFilteredTransitionExecutor[SnapshotT] extends ExecutorBase[SnapshotT] {
  test("filtered check enabled and discard") { exeCtx: ExecutorContextT =>
    // x' <- 1 /\ y' <- 1
    val init = tla.and(mkAssign("y", 1), mkAssign("x", 1))
    // x' <- x /\ y' <- x + y
    val next1 = tla.and(mkAssign("x", tla.name("x")), mkAssign("y", tla.plus(tla.name("x"), tla.name("y"))))
    val next2 = tla.and(
        mkAssign("x", tla.name("y")),
        mkAssign("y", tla.name("x")),
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
    val invFilter = "(0->.*|2->.*|3->state0|4->.*|5->state1|6->action1|7->action1)"
    val trex = new FilteredTransitionExecutor[SnapshotT](transFilter, invFilter, impl)
    trex.prepareTransition(1, init)
    trex.pickTransition()
    trex.nextState()
    // prepare Next
    trex.prepareTransition(1, nextTrans)
    // Step 1: Both invariants are excluded by the filter (no word starting in `1->`).
    // inv0 == x >= 3 (unchanged by `Next`)
    // inv1 == y >= x (maybe changed by `Next`)
    val inv0 = tla.ge(tla.name("x"), tla.int(3))
    val mayChange0 = trex.mayChangeAssertion(1, StateInvariant, 0, inv0)
    assert(!mayChange0)
    val inv1 = tla.ge(tla.name("y"), tla.name("x"))
    val mayChange1 = trex.mayChangeAssertion(1, StateInvariant, 1, inv1)
    assert(!mayChange1)
    trex.pickTransition()
    trex.nextState()
    // prepare Next
    trex.prepareTransition(1, nextTrans)
    // Step 2: Both invariants are included by the filter.
    //         Both may have changed, as the invariant filter excluded them both in the previous step.
    val mayChange20 = trex.mayChangeAssertion(1, StateInvariant, 0, inv0)
    assert(mayChange20)
    val mayChange21 = trex.mayChangeAssertion(1, StateInvariant, 1, inv1)
    assert(mayChange21)
    trex.pickTransition()
    trex.nextState()
    // prepare Next
    trex.prepareTransition(1, nextTrans)
    // Step 3: Only state invariant 0 is included by the filter.
    //         State invariant 0 is not changed by `next` (and was included in the last state).
    //         State invariant 1 is ignored by the filter.
    val mayChange30 = trex.mayChangeAssertion(1, StateInvariant, 0, inv0)
    assert(!mayChange30)
    val mayChange31 = trex.mayChangeAssertion(1, StateInvariant, 1, inv1)
    assert(!mayChange31)
    trex.pickTransition()
    trex.nextState()
    // prepare Next
    trex.prepareTransition(1, nextTrans)
    // Step 4: Both invariants are included by the filter.
    //         State invariant 0 is not changed by `next` (and was included in the last state).
    //         State invariant 1 may have changed, as the invariant filter excluded it in the previous step.
    val mayChange40 = trex.mayChangeAssertion(1, StateInvariant, 0, inv0)
    assert(!mayChange40)
    val mayChange41 = trex.mayChangeAssertion(1, StateInvariant, 1, inv1)
    assert(mayChange41)
    trex.pickTransition()
    trex.nextState()
    // prepare Next
    trex.prepareTransition(1, nextTrans)
    // Step 5: Only state invariant 1 is included by the filter.
    //         State invariant 0 is excluded by the filter
    //         State invariant 1 is included by the filter, was included at the previous step, and may change.
    val mayChange50 = trex.mayChangeAssertion(1, StateInvariant, 0, inv0)
    assert(!mayChange50)
    val mayChange51 = trex.mayChangeAssertion(1, StateInvariant, 1, inv1)
    assert(mayChange51)
    trex.pickTransition()
    trex.nextState()
    // prepare Next
    trex.prepareTransition(1, nextTrans)
    // Step 6: Both state invariants are excluded by the filter.
    val mayChange60 = trex.mayChangeAssertion(1, StateInvariant, 0, inv0)
    assert(!mayChange60)
    val mayChange61 = trex.mayChangeAssertion(1, StateInvariant, 1, inv1)
    assert(!mayChange61)
    trex.pickTransition()
    trex.nextState()
    // prepare Next
    trex.prepareTransition(1, nextTrans)
    // Step 7: Pretend that both invariants are action invariants; the 2nd is included by the filter.
    val mayChange70 = trex.mayChangeAssertion(1, ActionInvariant, 0, inv0)
    assert(!mayChange70)
    val mayChange71 = trex.mayChangeAssertion(1, ActionInvariant, 1, inv1)
    assert(mayChange71)
  }

  test("filtered regression on #108") { exeCtx: ExecutorContextT =>
    // y' <- 1
    val init = tla.and(mkAssign("y", 1))
    // y' <- y + 1
    val nextTrans = mkAssign("y", tla.plus(tla.name("y"), tla.int(1)))
    // push Init
    val invFilter = "(1->.*|2->.*)"
    val impl = new TransitionExecutorImpl(Set.empty, Set("y"), exeCtx)
    val trex = new FilteredTransitionExecutor[SnapshotT]("", invFilter, impl)
    trex.prepareTransition(1, init)
    trex.pickTransition()
    // the user told us not to check the invariant in state 0
    val notInv = tla.bool(false)
    val mayChange1 = trex.mayChangeAssertion(1, StateInvariant, 0, notInv)
    assert(!mayChange1)
    trex.nextState()
    // apply Next
    trex.prepareTransition(1, nextTrans)
    // we must check the invariant right now, as it was skipped earlier
    val mayChange2 = trex.mayChangeAssertion(1, StateInvariant, 0, notInv)
    assert(mayChange2)
    trex.pickTransition()
    trex.nextState()
    // apply Next
    trex.prepareTransition(1, nextTrans)
    // this time we should skip the check
    val mayChange3 = trex.mayChangeAssertion(1, StateInvariant, 0, notInv)
    assert(!mayChange3)
  }

  private def mkAssign(name: String, value: Int) =
    tla.assignPrime(tla.name(name), tla.int(value))

  private def mkAssign(name: String, rhs: TlaEx) =
    tla.assignPrime(tla.name(name), rhs)
}
