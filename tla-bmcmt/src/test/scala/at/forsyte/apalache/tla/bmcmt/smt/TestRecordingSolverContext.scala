package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}
import at.forsyte.apalache.tla.typecomp._
import org.scalatest.funsuite.AnyFunSuite

/**
 * [[RecordingSolverContext]] tests. Override [[AnyFunSuite.withFixture]] to set up specific solver contexts (e.g., for
 * different encodings).
 */
trait TestRecordingSolverContext extends AnyFunSuite {
  protected var solverConfig: SolverConfig = _

  private val int42: BuilderT = tla.int(42)

  test("operations proxied") {
    val solver = RecordingSolverContext.createZ3(None, solverConfig)
    val arena = PureArenaAdapter.create(solver).appendCell(IntT1)
    val x = arena.topCell
    solver.assertGroundExpr(tla.eql(x.toBuilder, int42))
    assert(solver.sat())
    assert(solver.evalGroundExpr(x.toBuilder) == int42.build)
  }

  test("write and read") {
    val solver = RecordingSolverContext.createZ3(None, solverConfig)
    val arena = PureArenaAdapter.create(solver).appendCell(IntT1)
    val x = arena.topCell
    solver.assertGroundExpr(tla.eql(x.toBuilder, int42))
    assert(solver.sat())
    assert(solver.evalGroundExpr(x.toBuilder) == int42.build)
    // save the log
    val log = solver.extractLog()
    // update the context
    solver.assertGroundExpr(tla.gt(x.toBuilder, tla.int(1000)))
    assert(!solver.sat())
    // restore the context
    val restoredSolver = RecordingSolverContext.createZ3(Some(log), solverConfig)
    // the restored context should be satisfiable
    assert(restoredSolver.sat())
    assert(restoredSolver.evalGroundExpr(x.toBuilder) == int42.build)
  }

  test("pop on empty") {
    val solver = RecordingSolverContext.createZ3(None, solverConfig)
    assertThrows[IllegalArgumentException](solver.pop(2))
  }
}
