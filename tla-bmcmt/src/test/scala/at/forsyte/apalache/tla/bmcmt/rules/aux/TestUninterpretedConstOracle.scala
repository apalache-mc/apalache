package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.{Binding, RewriterBase, SymbState}
import at.forsyte.apalache.tla.lir.{BoolT1, TestingPredefs}
import at.forsyte.apalache.tla.types.{tlaU => tla}
import at.forsyte.apalache.tla.typecomp._

trait TestUninterpretedConstOracle extends RewriterBase with TestingPredefs {
  test("""UninterpretedConst Oracle.create""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    val state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    UninterpretedConstOracle.create(rewriter, state, 6)
    assert(solverContext.sat())
  }

  test("""UninterpretedConst Oracle.whenEqualTo""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    val state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    val (nextState, oracle) = UninterpretedConstOracle.create(rewriter, state, 6)
    assert(solverContext.sat())
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 3))
    assert(solverContext.sat())
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 4))
    assert(!solverContext.sat())
  }

  test("""UninterpretedConst Oracle.evalPosition""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    val state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle
    val (nextState, oracle) = UninterpretedConstOracle.create(rewriter, state, 6)
    assert(solverContext.sat())
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 3))
    assert(solverContext.sat())
    val position = oracle.evalPosition(rewriter.solverContext, nextState)
    assert(3 == position)
  }

  test("""UninterpretedConst Oracle.caseAssertions""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    state = state.updateArena(_.appendCell(BoolT1))
    val flag = state.arena.topCell
    // introduce an oracle
    val (nextState, oracle) = UninterpretedConstOracle.create(rewriter, state, 2)
    // assert flag == true iff oracle = 0
    rewriter.solverContext
      .assertGroundExpr(oracle.caseAssertions(nextState, Seq(flag.toBuilder, tla.not(flag.toBuilder))))
    // assert oracle = 1
    rewriter.push()
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 1))
    assert(solverContext.sat())
    val expected1 = tla.bool(false).build
    assert(expected1 == solverContext.evalGroundExpr(flag.toBuilder))
    rewriter.pop()
    // assert oracle = 0
    rewriter.push()
    rewriter.solverContext.assertGroundExpr(oracle.whenEqualTo(nextState, 0))
    assert(solverContext.sat())
    val expected2 = tla.bool(true).build
    assert(expected2 == solverContext.evalGroundExpr(flag.toBuilder))
    rewriter.pop()
  }
}
