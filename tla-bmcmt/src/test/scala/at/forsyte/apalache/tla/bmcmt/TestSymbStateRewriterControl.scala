package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterControl extends RewriterBase with TestingPredefs {
  private val types = Map(
      "b" -> BoolT1(),
      "i" -> IntT1(),
      "I" -> SetT1(IntT1()),
      "O" -> OperT1(Seq(), IntT1())
  )

  test("""IF 3 > 2 THEN 2 < 4 ELSE 5 < 1""") { rewriter: SymbStateRewriter =>
    val pred = gt(int(3), int(2))
    val e1 = lt(int(2), int(4))
    val e2 = lt(int(5), int(1))
    val ifThenElse = ite(pred ? "b", e1 ? "b", e2 ? "b")
      .typed(types, "b")

    val state = new SymbState(ifThenElse, arena, Binding())
    assertTlaExAndRestore(rewriter, state.setRex(ifThenElse))
  }

  test("""IF 3 < 2 THEN 2 < 4 ELSE 5 < 1""") { rewriter: SymbStateRewriter =>
    val pred = lt(int(3), int(2))
    val e1 = lt(int(2), int(4))
    val e2 = lt(int(5), int(1))
    val ifThenElse = not(ite(pred ? "b", e1 ? "b", e2 ? "b") ? "b")
      .typed(types, "b")

    val state = new SymbState(ifThenElse, arena, Binding())
    assertTlaExAndRestore(rewriter, state.setRex(ifThenElse))
  }

  test("""IF 3 > 2 THEN 4 ELSE 1""") { rewriter: SymbStateRewriter =>
    val pred = gt(int(3), int(2))
    val e1 = int(4)
    val e2 = int(1)
    val ifThenElse = ite(pred ? "b", e1, e2) ? "i"
    val eq4 = eql(ifThenElse, int(4))
      .typed(types, "b")

    val state = new SymbState(eq4, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""IF 3 < 2 THEN 4 ELSE 1""") { rewriter: SymbStateRewriter =>
    val pred = lt(int(3), int(2))
    val e1 = int(4)
    val e2 = int(1)
    val ifThenElse = ite(pred ? "b", e1, e2) ? "i"
    val eq4 = eql(ifThenElse, int(1))
      .typed(types, "b")

    val state = new SymbState(eq4, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""IF 3 < 2 THEN {1, 2} ELSE {2, 3} equals {2, 3}""") { rewriter: SymbStateRewriter =>
    val pred = lt(int(3), int(2))
    val e1 = enumSet(int(1), int(2))
    val e2 = enumSet(int(2), int(3))
    val ifThenElse = ite(pred ? "b", e1 ? "I", e2 ? "I")
      .typed(types, "I")
    val eq23 = eql(ifThenElse, e2 ? "I")
      .typed(types, "b")

    val state = new SymbState(eq23, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""IF 1 = 1 THEN {2} ELSE {1} ]""") { rewriter: SymbStateRewriter =>
    val ifThenElse = ite(eql(int(1), int(1)) ? "b", enumSet(int(2)) ? "I", enumSet(int(1)) ? "I")
    val eq = eql(enumSet(int(2)) ? "I", ifThenElse ? "I")
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-ITE[5]: IF 2 < 3 THEN {1, 2} ELSE {2, 3} ~~> {1, 2}""") { rewriter: SymbStateRewriter =>
    val pred = lt(int(2), int(3))
    val e1 = enumSet(int(1), int(2))
    val e2 = enumSet(int(2), int(3))
    val ifThenElse = ite(pred ? "b", e1 ? "I", e2 ? "I")
      .typed(types, "I")
    val eq = eql(ifThenElse, e1 ? "I")
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""1 + (IF 3 < 2 THEN 4 ELSE 1)""") { rewriter: SymbStateRewriter =>
    val pred = lt(int(3), int(2))
    val e1 = int(4)
    val e2 = int(1)
    val addition = plus(int(1), ite(pred ? "b", e1 ? "i", e2 ? "i") ? "i")
    val eq = eql(addition ? "i", int(2))
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  // LET-IN is often used to cache computation results
  test("""LET A == 1 + 2 IN 1 + A equals 4""") { rewriter: SymbStateRewriter =>
    val decl = declOp("A", plus(int(1), int(2)) ? "i")
      .typedOperDecl(types, "O")
    val let = letIn(plus(int(1), appOp(name("A") ? "O") ? "i") ? "i", decl)
      .typed(types, "i")
    val state = new SymbState(let, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    val eq = eql(nextState.ex ? "i", int(4))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }
}
