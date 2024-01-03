package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.{Binding, RewriterBase, SymbState}
import at.forsyte.apalache.tla.lir.{BoolT1, TestingPredefs}
import at.forsyte.apalache.tla.types.tla

trait TestSparseOracle extends RewriterBase with TestingPredefs {
  test("""Sparse Oracle.create""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    val state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    val (_, oracle) = PropositionalOracle.create(rewriter, state, 2)
    new SparseOracle(oracle, Set(1, 10))
    assert(solverContext.sat())
  }

  test("""Sparse Oracle.whenEqualTo""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    val state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    val (nextState, oracle) = PropositionalOracle.create(rewriter, state, 3)
    val sparseOracle = new SparseOracle(oracle, Set(1, 5, 10))
    assert(solverContext.sat())
    rewriter.solverContext.assertGroundExpr(sparseOracle.whenEqualTo(nextState, 5))
    assert(solverContext.sat())
  }

  test("""Sparse Oracle.evalPosition""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    val state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    val (nextState, oracle) = PropositionalOracle.create(rewriter, state, 3)
    val sparseOracle = new SparseOracle(oracle, Set(1, 5, 10))
    assert(solverContext.sat())
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 5))
    assert(solverContext.sat())
    val position = sparseOracle.evalPosition(rewriter.solverContext, nextState)
    assert(5 == position)
  }

  test("""Sparse Oracle.caseAssertions""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    state = state.updateArena(_.appendCell(BoolT1))
    val flag = state.arena.topCell
    // introduce an oracle
    val (nextState, oracle) = PropositionalOracle.create(rewriter, state, 2)
    val sparseOracle = new SparseOracle(oracle, Set(1, 5))
    // assert flag == true iff oracle = 1
    rewriter.solverContext
      .assertGroundExpr(sparseOracle.caseAssertions(nextState, Seq(flag.toBuilder, tla.not(flag.toBuilder))))
    // assert oracle = 5
    rewriter.push()
    rewriter.solverContext.assertGroundExpr(sparseOracle.whenEqualTo(nextState, 5))
    assert(solverContext.sat())
    val expected1 = tla.bool(false).build
    assert(expected1 == solverContext.evalGroundExpr(flag.toBuilder))
    rewriter.pop()
    // assert oracle = 1
    rewriter.push()
    rewriter.solverContext.assertGroundExpr(sparseOracle.whenEqualTo(nextState, 1))
    assert(solverContext.sat())
    val expected2 = tla.bool(true).build
    assert(expected2 == solverContext.evalGroundExpr(flag.toBuilder))
    rewriter.pop()
  }
}
