package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.values.TlaIntSet
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterRecFun extends RewriterBase with TestingPredefs {
  test(
    """recursive fun: f[n \in { 1, 2, 3 }] == IF n <= 1 THEN 2 ELSE 2 * f[n - 1]"""
  ) {
    import tla._

    val set = enumSet(tla.int(1), tla.int(2), tla.int(3))

    val ref = tla.withType(
      tla.recFunRef(),
      tla.funSet(ValEx(TlaIntSet), ValEx(TlaIntSet))
    )

    val map = ite(
      le(tla.name("n"), int(1)),
      int(2),
      mult(int(2), appFun(ref, minus(tla.name("n"), int(1))))
    ) ///

    val fun = recFunDef(map, tla.name("n"), set)

    val rewriter = create()
    var state = rewriter.rewriteUntilDone(new SymbState(fun, arena, Binding()))
    val funCell = state.ex

    def resEq(i: Int, j: Int) = eql(int(j), appFun(funCell, int(i)))

    assertTlaExAndRestore(rewriter, state.setRex(resEq(1, 2)))
    assertTlaExAndRestore(rewriter, state.setRex(resEq(2, 4)))
    assertTlaExAndRestore(rewriter, state.setRex(resEq(3, 8)))
  }
}
