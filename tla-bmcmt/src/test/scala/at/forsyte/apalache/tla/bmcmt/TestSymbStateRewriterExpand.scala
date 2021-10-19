package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, IntT1, SetT1}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterExpand extends RewriterBase {
  private val types = Map(
      "b" -> BoolT1(),
      "i" -> IntT1(),
      "I" -> SetT1(IntT1()),
      "II" -> SetT1(SetT1(IntT1())),
      "B" -> SetT1(BoolT1()),
      "i_TO_b" -> SetT1(FunT1(IntT1(), BoolT1()))
  )

  test("""Expand(SUBSET {1, 2})""") { rewriterType: String =>
    val baseset = enumSet(int(1), int(2))
    val expandPowset = apalacheExpand(powSet(baseset ? "I") ? "II")
      .typed(types, "II")
    val subsets = enumSet(enumSet() ? "I", enumSet(int(1)) ? "I", enumSet(int(2)) ? "I", enumSet(int(1), int(2)) ? "I")
    val eq = eql(expandPowset, subsets ? "II")
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Expand([{1, 2, 3} -> {FALSE, TRUE}]) fails as unsupported""") { rewriterType: String =>
    val domain = enumSet(int(1), int(2), int(3))
    val codomain = enumSet(bool(false), bool(true))
    val set = apalacheExpand(funSet(domain ? "I", codomain ? "B") ? "i_TO_b")
      .typed(types, "i_TO_b")
    val state = new SymbState(set, arena, Binding())
    val rewriter = create(rewriterType)
    assertThrows[RewriterException](rewriter.rewriteUntilDone(state))
  }
}
