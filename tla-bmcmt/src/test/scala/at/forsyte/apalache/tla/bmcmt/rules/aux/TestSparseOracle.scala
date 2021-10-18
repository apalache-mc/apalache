package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.bmcmt.{Binding, RewriterBase, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSparseOracle extends RewriterBase with TestingPredefs {
  test("""Oracle.create""") { rewriter: SymbStateRewriter =>
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    val (nextState, oracle) = PropositionalOracle.create(rewriter, state, 2)
    val sparseOracle = new SparseOracle(oracle, Set(1, 10))
    assert(solverContext.sat())
  }

  test("""Oracle.whenEqualTo""") { rewriter: SymbStateRewriter =>
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    val (nextState, oracle) = PropositionalOracle.create(rewriter, state, 3)
    val sparseOracle = new SparseOracle(oracle, Set(1, 5, 10))
    assert(solverContext.sat())
    rewriter.solverContext.assertGroundExpr(sparseOracle.whenEqualTo(nextState, 5))
    assert(solverContext.sat())
  }

  test("""Oracle.evalPosition""") { rewriter: SymbStateRewriter =>
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    val (nextState, oracle) = PropositionalOracle.create(rewriter, state, 3)
    val sparseOracle = new SparseOracle(oracle, Set(1, 5, 10))
    assert(solverContext.sat())
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 5))
    assert(solverContext.sat())
    val position = sparseOracle.evalPosition(rewriter.solverContext, nextState)
    assert(5 == position)
  }

  test("""Oracle.caseAssertions""") { rewriter: SymbStateRewriter =>
    var state = new SymbState(tla.bool(true), arena, Binding())
    state = state.updateArena(_.appendCell(BoolT()))
    val flag = state.arena.topCell
    // introduce an oracle
    val (nextState, oracle) = PropositionalOracle.create(rewriter, state, 2)
    val sparseOracle = new SparseOracle(oracle, Set(1, 5))
    // assert flag == true iff oracle = 1
    rewriter.solverContext
      .assertGroundExpr(sparseOracle.caseAssertions(nextState, Seq(flag.toNameEx, tla.not(flag.toNameEx))))
    // assert oracle = 5
    rewriter.push()
    rewriter.solverContext.assertGroundExpr(sparseOracle.whenEqualTo(nextState, 5))
    assert(solverContext.sat())
    val expected1 = tla.bool(false).untyped()
    assert(expected1 == solverContext.evalGroundExpr(flag.toNameEx))
    rewriter.pop()
    // assert oracle = 1
    rewriter.push()
    rewriter.solverContext.assertGroundExpr(sparseOracle.whenEqualTo(nextState, 1))
    assert(solverContext.sat())
    val expected2 = tla.bool(true).untyped()
    assert(expected2 == solverContext.evalGroundExpr(flag.toNameEx))
    rewriter.pop()
  }
}
