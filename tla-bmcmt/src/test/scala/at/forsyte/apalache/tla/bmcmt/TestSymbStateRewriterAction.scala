package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter.Continue
import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterAction extends RewriterBase {
  test("""SE-PRIME: x' ~~> NameEx(x')""") {
    val state = new SymbState(tla.prime(NameEx("x")), CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case Continue(next) =>
        assert(next.ex == NameEx("x'"))

      case _ =>
        fail("Expected x to be renamed to x'")
    }
  }
}
