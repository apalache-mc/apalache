package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.BoolT1

trait TestSymbStateRewriterStr extends RewriterBase {
  test(""" rewrite "red" """) { rewriterType: SMTEncoding =>
    val neq = not(eql(str("red"), str("blue")).typed(BoolT1()))
      .typed(BoolT1())

    val state = new SymbState(neq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }
}
