package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.bmcmt.{Binding, RewriterBase, SymbState}
import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestPropositionalOracle extends RewriterBase with TestingPredefs {
  test("""Oracle.create""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    val (nextState, oracle) = PropositionalOracle.create(rewriter, state, 6)
    assert(solverContext.sat())
  }

  test("""Oracle.whenEqualTo""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    val (nextState, oracle) = PropositionalOracle.create(rewriter, state, 6)
    assert(solverContext.sat())
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 3))
    assert(solverContext.sat())
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 4))
    assert(!solverContext.sat())
  }

  test("""Oracle.evalPosition""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    val (nextState, oracle) = PropositionalOracle.create(rewriter, state, 6)
    assert(solverContext.sat())
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 3))
    assert(solverContext.sat())
    val position = oracle.evalPosition(rewriter.solverContext, nextState)
    assert(3 == position)
  }

  test("""Oracle.caseAssertions""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), arena, Binding())
    state = state.updateArena(_.appendCell(BoolT()))
    val flag = state.arena.topCell
    // introduce an oracle
    val (nextState, oracle) = PropositionalOracle.create(rewriter, state, 2)
    // assert flag == true iff oracle = 0
    rewriter.solverContext
      .assertGroundExpr(oracle.caseAssertions(nextState, Seq(flag.toNameEx, tla.not(flag.toNameEx))))
    // assert oracle = 1
    rewriter.push()
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 1))
    assert(solverContext.sat())
    assert(solverContext.evalGroundExpr(flag.toNameEx) == tla.bool(false))
    rewriter.pop()
    // assert oracle = 0
    rewriter.push()
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 0))
    assert(solverContext.sat())
    assert(solverContext.evalGroundExpr(flag.toNameEx) == tla.bool(true))
    rewriter.pop()
  }
}
