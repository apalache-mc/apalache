package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter.Continue
import at.forsyte.apalache.tla.lir.{IntT1, NameEx}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._

trait TestSymbStateRewriterAction extends RewriterBase {
  test("""x' is rewritten to the binding of x'""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    arena.appendCell(IntT1) // the type finder is strict about unassigned types, so let's create a cell for x'
    val state = new SymbState(tla.prime(NameEx("x")), arena, Binding("x'" -> arena.topCell))
    rewriter.rewriteOnce(state) match {
      case Continue(next) =>
        assert(next.ex == NameEx("x'"))

      case _ =>
        fail("Expected x to be renamed to x'")
    }
  }
}
