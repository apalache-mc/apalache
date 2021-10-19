package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.{BoolT1, StrT1}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterStr extends RewriterBase {
  test(""" rewrite "red" """) { rewriterType: String =>
    val string = str("red").typed(StrT1())
    val neq = not(eql(str("red"), str("blue")).typed(BoolT1()))
      .typed(BoolT1())

    val state = new SymbState(neq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }
}
