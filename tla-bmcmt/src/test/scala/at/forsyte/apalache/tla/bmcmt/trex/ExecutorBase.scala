package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.scalatest.fixture

trait ExecutorBase[SnapshotT] extends fixture.FunSuite {
  type ExecutorContextT = ExecutionContext[SnapshotT]
  type FixtureParam = ExecutorContextT

  protected def assertValid(trex: TransitionExecutorImpl[SnapshotT], assertion: TlaEx): Unit = {
    var snapshot = trex.snapshot()
    trex.assertState(assertion)
    assert(trex.sat(0).contains(true))
    trex.recover(snapshot)

    snapshot = trex.snapshot()
    trex.assertState(tla.not(assertion))
    assert(trex.sat(0).contains(false))
    trex.recover(snapshot)
  }
}
