package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.BmcOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterExpand extends RewriterBase {
  test("""Expand(SUBSET {1, 2})""") {
    val baseset = tla.enumSet(tla.int(1), tla.int(2))
    val expandPowset = OperEx(BmcOper.expand, tla.powSet(baseset))
    val state = new SymbState(expandPowset, CellTheory(), arena, new Binding)
    val rewriter = create()
    var nextState = rewriter.rewriteUntilDone(state)
    val powCell = nextState.asCell
    // check equality
    val eq = tla.eql(nextState.ex,
      tla.enumSet(tla.withType(tla.enumSet(), AnnotationParser.toTla(FinSetT(IntT()))),
        tla.enumSet(tla.int(1)),
        tla.enumSet(tla.int(2)),
          tla.enumSet(tla.int(1), tla.int(2))))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""Expand([{1, 2, 3} -> {FALSE, TRUE}]) should fail""") {
    val domain = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val codomain = tla.enumSet(tla.bool(false), tla.bool(true))
    val funSet = OperEx(BmcOper.expand, tla.funSet(domain, codomain))
    val state = new SymbState(funSet, CellTheory(), arena, new Binding)
    val rewriter = create()
    assertThrows[RewriterException](rewriter.rewriteUntilDone(state))
  }

}
