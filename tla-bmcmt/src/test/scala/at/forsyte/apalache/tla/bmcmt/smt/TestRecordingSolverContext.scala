package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.tla.bmcmt.Arena
import at.forsyte.apalache.tla.bmcmt.types.IntT
import at.forsyte.apalache.tla.lir.{BuilderVal, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestRecordingSolverContext extends FunSuite {
  private val defaultSolverConfig = SolverConfig(debug = false, profile = false, randomSeed = 0)

  private val int42: TlaEx = tla.int(42)

  test("operations proxied") {
    val solver = RecordingSolverContext.createZ3(None, defaultSolverConfig)
    var arena = Arena.create(solver).appendCell(IntT())
    val x = arena.topCell
    solver.assertGroundExpr(tla.eql(x.toNameEx, int42))
    assert(solver.sat())
    assert(solver.evalGroundExpr(x.toNameEx) == int42)
  }

  test("write and read") {
    val solver = RecordingSolverContext.createZ3(None, defaultSolverConfig)
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
    val restoredSolver = RecordingSolverContext.createZ3(Some(log), defaultSolverConfig)
    // the restored context should be satisfiable
    assert(restoredSolver.sat())
    assert(restoredSolver.evalGroundExpr(x.toNameEx) == int42)
  }

  test("pop on empty") {
    val solver = RecordingSolverContext.createZ3(None, defaultSolverConfig)
    assertThrows[IllegalArgumentException](solver.pop(2))
  }
}
