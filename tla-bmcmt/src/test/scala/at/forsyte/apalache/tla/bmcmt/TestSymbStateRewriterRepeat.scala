package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterRepeat extends RewriterBase {
  test("""Repeat(LET Op(a,i) == a + 1 IN Op, 5, 0) = 5""") { rewriterType: SMTEncoding =>
    // Op(x, i) == x + 1
    val opT = OperT1(Seq(IntT1, IntT1), IntT1)

    val plusOneEx = tla.plus(tla.name("x", IntT1), tla.int(1))
    val plusOneOper = tla.decl("Op", plusOneEx, tla.param("x", IntT1), tla.param("i", IntT1))
    val letEx = tla.letIn(tla.name(plusOneOper.name, opT), plusOneOper)
    val repeatEx = tla.repeat(letEx, 5, tla.int(0))

    val rewriter = create(rewriterType)
    var state = new SymbState(repeatEx, arena, Binding())
    state = rewriter.rewriteUntilDone(state)
    val asCell = state.asCell

    // compare the value
    val eqn = tla.eql(asCell.toBuilder, tla.int(5))
    assertTlaExAndRestore(rewriter, state.setRex(eqn))
  }

  test("""Repeat(LET Op(a,i) == a + i IN Op, 5, 0) = 15""") { rewriterType: SMTEncoding =>
    // Op(x, i) == x + i
    val opT = OperT1(Seq(IntT1, IntT1), IntT1)

    val plusiEx = tla.plus(tla.name("x", IntT1), tla.name("i", IntT1))
    val plusiOper = tla.decl("Op", plusiEx, tla.param("x", IntT1), tla.param("i", IntT1))
    val letEx = tla.letIn(tla.name(plusiOper.name, opT), plusiOper)
    val repeatEx = tla.repeat(letEx, 5, tla.int(0))

    val rewriter = create(rewriterType)
    var state = new SymbState(repeatEx, arena, Binding())
    state = rewriter.rewriteUntilDone(state)
    val asCell = state.asCell

    // compare the value
    val eqn = tla.eql(asCell.toBuilder, tla.int(15))
    assertTlaExAndRestore(rewriter, state.setRex(eqn))
  }
}
