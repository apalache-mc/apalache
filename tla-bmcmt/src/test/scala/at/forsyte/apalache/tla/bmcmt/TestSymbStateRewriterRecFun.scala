package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._

trait TestSymbStateRewriterRecFun extends RewriterBase with TestingPredefs {
  private val types =
    Map(
        "b" -> BoolT1(),
        "i" -> IntT1(),
        "I" -> SetT1(IntT1()),
        "i_to_i" -> FunT1(IntT1(), IntT1())
    )

  test("""recursive fun: f[n \in { 1, 2, 3 }] == IF n <= 1 THEN 2 ELSE 2 * f[n - 1]""") { rewriterType: String =>
    val set = enumSet(int(1), int(2), int(3)) ? "I"
    val ref = recFunRef() ? "i_to_i"

    val map = ite(
        le(name("n") ? "i", int(1)) ? "b",
        int(2),
        mult(int(2), appFun(ref, minus(name("n") ? "i", int(1)) ? "i") ? "i") ? "i"
    ).typed(types, "i")

    val fun = recFunDef(map, name("n") ? "i", set)
      .typed(types, "i_to_i")

    val rewriter = create(rewriterType)
    var state = rewriter.rewriteUntilDone(new SymbState(fun, arena, Binding()))
    val funCell = state.ex

    def resEq(i: Int, j: Int) = {
      eql(int(j), appFun(funCell ? "i_to_i", int(i)) ? "i")
        .typed(types, "b")
    }

    assertTlaExAndRestore(rewriter, state.setRex(resEq(1, 2)))
    assertTlaExAndRestore(rewriter, state.setRex(resEq(2, 4)))
    assertTlaExAndRestore(rewriter, state.setRex(resEq(3, 8)))
  }
}
