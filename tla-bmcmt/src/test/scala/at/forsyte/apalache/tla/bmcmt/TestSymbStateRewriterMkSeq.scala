package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterMkSeq extends RewriterBase {
  test("""MkSeq(3, LAMBDA x: x + 1) = << 2, 3, 4 >>""") { rewriterType: SMTEncoding =>
    // A(x) == x + 1
    val intT = IntT1

    val plusOneEx = tla.plus(tla.name("x", intT), tla.int(1))
    val letEx = tla.lambda("A", plusOneEx, tla.param("x", intT))
    val seqEx = tla.mkSeq(3, letEx)
    val rewriter = create(rewriterType)
    var state = new SymbState(seqEx, arena, Binding())
    state = rewriter.rewriteUntilDone(state.setRex(seqEx))
    val seqCell = state.asCell

    // compare the length
    val eqn = tla.eql(tla.len(tla.unchecked(seqCell.toNameEx)), tla.int(3))
    assertTlaExAndRestore(rewriter, state.setRex(eqn))

    // compare the elements
    for (i <- 1.to(3)) {
      val eqn = tla.eql(tla.app(tla.unchecked(seqCell.toNameEx), tla.int(i)), tla.int(i + 1))
      assertTlaExAndRestore(rewriter, state.setRex(eqn))
    }
  }

  test("""MkSeq(0, LAMBDA x: x + 1) = << >>""") { rewriterType: SMTEncoding =>
    // A(x) == x + 1
    val intT = IntT1

    val plusOneEx = tla.plus(tla.name("x", intT), tla.int(1))
    val letEx = tla.lambda("A", plusOneEx, tla.param("x", intT))
    val seqEx = tla.mkSeq(0, letEx)

    val eqn = tla.eql(tla.len(seqEx), tla.int(0))
    val state = new SymbState(eqn, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }
}
