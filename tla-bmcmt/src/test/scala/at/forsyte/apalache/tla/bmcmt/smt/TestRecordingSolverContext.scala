package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.tla.bmcmt.{Arena, EncodingBase}
import at.forsyte.apalache.tla.bmcmt.types.IntT
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.scalatest.fixture

trait TestRecordingSolverContext extends fixture.FunSuite with EncodingBase {
  protected type FixtureParam = Any

  protected var solverConfig: SolverConfig = _

  private val int42: TlaEx = tla.int(42)

  test("operations proxied") { _ =>
    val solver = RecordingSolverContext.createZ3(None, solverConfig)
    var arena = Arena.create(solver).appendCell(IntT())
    val x = arena.topCell
    solver.assertGroundExpr(tla.eql(x.toNameEx, int42))
    assert(solver.sat())
    assert(solver.evalGroundExpr(x.toNameEx) == int42)
  }

  test("write and read") { _ =>
    val solver = RecordingSolverContext.createZ3(None, solverConfig)
    var arena = Arena.create(solver).appendCell(IntT())
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

  test("pop on empty") { _ =>
    val solver = RecordingSolverContext.createZ3(None, solverConfig)
    assertThrows[IllegalArgumentException](solver.pop(2))
  }
}
