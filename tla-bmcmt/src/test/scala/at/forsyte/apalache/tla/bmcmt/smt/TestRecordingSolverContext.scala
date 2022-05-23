package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.tla.bmcmt.Arena
import at.forsyte.apalache.tla.lir.{IntT1, TlaEx}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import org.scalatest.funsuite.AnyFunSuite

/**
 * [[RecordingSolverContext]] tests. Override [[AnyFunSuite.withFixture]] to set up specific solver contexts (e.g., for
 * different encodings).
 */
trait TestRecordingSolverContext extends AnyFunSuite {
  protected var solverConfig: SolverConfig = _

  private val int42: TlaEx = tla.int(42)

  test("operations proxied") {
    val solver = RecordingSolverContext.createZ3(None, solverConfig)
    val arena = Arena.create(solver).appendCell(IntT1)
    val x = arena.topCell
    solver.assertGroundExpr(tla.eql(x.toNameEx, int42))
    assert(solver.sat())
    assert(solver.evalGroundExpr(x.toNameEx) == int42)
  }

  test("write and read") {
    val solver = RecordingSolverContext.createZ3(None, solverConfig)
    val arena = Arena.create(solver).appendCell(IntT1)
    val x = arena.topCell
    solver.assertGroundExpr(tla.eql(x.toNameEx, int42))
    assert(solver.sat())
    assert(solver.evalGroundExpr(x.toNameEx) == int42)
    // save the log
    val log = solver.extractLog()
    // update the context
    solver.assertGroundExpr(tla.gt(x.toNameEx, tla.int(1000)))
    assert(!solver.sat())
    // restore the context
    val restoredSolver = RecordingSolverContext.createZ3(Some(log), solverConfig)
    // the restored context should be satisfiable
    assert(restoredSolver.sat())
    assert(restoredSolver.evalGroundExpr(x.toNameEx) == int42)
  }

  test("pop on empty") {
    val solver = RecordingSolverContext.createZ3(None, solverConfig)
    assertThrows[IllegalArgumentException](solver.pop(2))
  }
}
