package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterStr extends RewriterBase {
  test(""" rewrite "red" """) { rewriterType: SMTEncoding =>
    val neq = tla.not(tla.eql(tla.str("red"), tla.str("blue")))

    val state = new SymbState(neq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }
}
