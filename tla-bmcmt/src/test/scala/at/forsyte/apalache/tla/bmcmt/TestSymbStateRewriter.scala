package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriter extends RewriterBase {
  test("SE-SUBST1: x[cell/x] ~~> cell") { rewriter: SymbStateRewriter =>
    arena = arena.appendCell(UnknownT())
    val cell = arena.topCell
    val binding = Binding("x" -> cell)
    val state = new SymbState(NameEx("x"), arena, binding)
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Done(nextState) =>
        val expected = NameEx("$C$%d".format(cell.id))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
