package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.infra.passes.options.SMTSolver
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.types.{tlaU => tla}
import at.forsyte.apalache.tla.typecomp._
import org.scalatest.funsuite.AnyFunSuite

class TestCvc5SolverContext extends AnyFunSuite {
  private val solverConfig = SolverConfig.default.copy(smtSolver = SMTSolver.CVC5, z3StatsSec = 0)

  override def withFixture(test: NoArgTest) = {
    assume(Cvc5SolverContext.isAvailable, "cvc5 native libraries are not available on this platform")
    super.withFixture(test)
  }

  test("assert and evaluate an integer cell") {
    val solver = new Cvc5SolverContext(solverConfig)
    try {
      val arena = PureArenaAdapter.create(solver).appendCell(IntT1)
      val x = arena.topCell

      solver.assertGroundExpr(tla.eql(x.toBuilder, tla.int(42)))

      assert(solver.sat())
      assert(solver.evalGroundExpr(x.toBuilder) == tla.int(42).build)
    } finally {
      solver.dispose()
    }
  }

  test("push and pop assertions") {
    val solver = new Cvc5SolverContext(solverConfig)
    try {
      val arena = PureArenaAdapter.create(solver).appendCell(IntT1)
      val x = arena.topCell

      solver.assertGroundExpr(tla.eql(x.toBuilder, tla.int(42)))
      assert(solver.sat())

      solver.push()
      solver.assertGroundExpr(tla.gt(x.toBuilder, tla.int(100)))
      assert(!solver.sat())

      solver.pop()
      assert(solver.sat())
    } finally {
      solver.dispose()
    }
  }
}
