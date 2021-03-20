package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.smt.{PreproSolverContext, SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.pp.TlaInputError
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterSet extends RewriterBase {
  private val types = Map(
      "i" -> IntT1(),
      "I" -> SetT1(IntT1()),
      "II" -> SetT1(SetT1(IntT1())),
      "III" -> SetT1(SetT1(SetT1(IntT1()))),
      "IV" -> SetT1(SetT1(SetT1(SetT1(IntT1())))),
      "V" -> SetT1(SetT1(SetT1(SetT1(SetT1(IntT1()))))),
      "b" -> BoolT1(),
      "B" -> SetT1(BoolT1()),
      "i_to_b" -> FunT1(IntT1(), BoolT1()),
      "ib" -> TupT1(IntT1(), BoolT1()),
      "IB" -> SetT1(TupT1(IntT1(), BoolT1()))
  )

  test("""{ x, y, z } ~~> c_set""") {
    val ex = enumSet(name("x") ? "i", name("y") ? "b", name("z") ? "b")
      .typed(types, "B")
    val binding = Binding("x" -> arena.cellFalse(), "y" -> arena.cellTrue(), "z" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case set @ NameEx(_) =>
            val falseInSet = in(arena.cellFalse().toNameEx ? "b", set ? "B")
              .typed(types, "b")
            solverContext.assertGroundExpr(falseInSet)
            assert(solverContext.sat())
            val notTrueInSet = not(in(arena.cellTrue().toNameEx ? "b", set ? "B") ? "b")
              .typed(types, "b")
            solverContext
              .assertGroundExpr(notTrueInSet)
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 3, 5} ~~> c_set""") {
    val ex = enumSet(int(1), int(3), int(5))
      .typed(types, "I")
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(_) =>
            assert(solverContext.sat())
          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{} \in {}""") {
    val ex = in(enumSet() ? "I", enumSet() ? "II")
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val nextState = create().rewriteUntilDone(state)
    assert(nextState.arena.cellFalse().toNameEx == nextState.ex)
  }

  test("""3 \in {1, 3, 5}""") {
    val ex = in(int(3), enumSet(int(1), int(3), int(5)) ? "I")
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{3} \in {{1}, {3}, {5}}""") {
    val ex = in(enumSet(int(3) ? "i") ? "I",
        enumSet(enumSet(int(1)) ? "I", enumSet(int(3)) ? "I", enumSet(int(5)) ? "I") ? "II")
      .typed(types, "b")

    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in {1, 3, 5}""") {
    val ex = in(int(2), enumSet(int(1), int(3), int(5)) ? "I")
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in Int""") {
    val ex = in(int(2), intSet() ? "I")
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  test("""2 \in Nat""") {
    val ex = in(int(2), natSet() ? "I")
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  test("""-1 \in Nat""") {
    val ex = in(int(-1), natSet() ? "I")
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState.setRex(not(nextState.ex ? "b").typed(types, "b")))
  }

  test("""~({} \in {})""") {
    val ex = not(in(enumSet() ? "I", enumSet() ? "II") ? "b")
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.push()
    solverContext.assertGroundExpr(not(nextState.ex ? "b").typed(types, "b"))
    assert(!solverContext.sat())
    solverContext.pop()
  }

  test("""FALSE \in {FALSE, TRUE}""") {
    val ex =
      in(bool(false), enumSet(bool(false), bool(true)) ? "B")
        .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx @ NameEx(name) =>
            rewriter.push()
            solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
            assert(!solverContext.sat())
            rewriter.pop()
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""~(FALSE \in {FALSE, TRUE})""") {
    val ex =
      not(in(bool(false), enumSet(bool(false), bool(true)) ? "B") ? "b")
        .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteUntilDone(state).ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""c_i \in {TRUE, TRUE}""") {
    arena = arena.appendCell(BoolT())
    val cell = arena.topCell
    val ex =
      in(cell.toNameEx ? "b", enumSet(bool(true), bool(true)) ? "B")
        .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx @ NameEx(name) =>
            rewriter.push()
            // cell = \TRUE
            solverContext.assertGroundExpr(eql(arena.cellTrue().toNameEx ? "b", cell.toNameEx ? "b").typed(types, "b"))
            // and membership holds true
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())
            rewriter.pop()
            // another query
            // cell = \FALSE
            solverContext.assertGroundExpr(eql(arena.cellFalse().toNameEx ? "b", cell.toNameEx ? "b").typed(types, "b"))
            // and membership holds true
            solverContext.assertGroundExpr(predEx)
            // contradiction
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""1 \in {1}""") {
    // regression: there is a special shortcut rule for singleton sets, which had a bug
    val ex = in(int(1), enumSet(int(1)) ? "I")
      .typed(types, "b")

    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        nextState.arena.appendCell(IntT()) // the buggy rule implementation triggered an error here
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assert(!solverContext.sat())
        rewriter.pop()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""~(Bool \in {TRUE, TRUE})""") {
    arena = arena.appendCell(BoolT())
    val cell = arena.topCell
    val ex =
      not(in(cell.toNameEx ? "b", enumSet(bool(true), bool(true)) ? "B") ? "b")
        .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteUntilDone(state).ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        // cell = TRUE
        solverContext.assertGroundExpr(eql(arena.cellTrue().toNameEx ? "b", cell.toNameEx ? "b").typed(types, "b"))
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        // another query
        // cell = \FALSE
        solverContext.assertGroundExpr(eql(arena.cellFalse().toNameEx ? "b", cell.toNameEx ? "b").typed(types, "b"))
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        // no contradiction here
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{}, {}}} \in {{}, {{}, {{}, {}}}}""") {
    def intSet() = enumSet().typed(types, "I")

    def int2Set() = enumSet().typed(types, "II")

    def int3Set() = enumSet().typed(types, "III")

    val left = enumSet(int2Set(), enumSet(intSet(), intSet()) ? "II")
      .typed(types, "III")
    val right = enumSet(int3Set(), enumSet(int2Set() ? "II", enumSet(intSet(), intSet()) ? "II") ? "III")
      .typed(types, "IV")
    val ex = in(left, right).typed(BoolT1())
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        // another query
        // and membership does not hold
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{{}}}} \in {{}, {{}, {{}}}""") {
    def intSet() = enumSet().typed(types, "I")

    def int2Set() = enumSet().typed(types, "II")

    def int3Set() = enumSet().typed(types, "III")

    def int4Set() = enumSet().typed(types, "IV")

    val left = enumSet(int3Set(), enumSet(enumSet(intSet()) ? "II") ? "III")
      .typed(types, "IV")
    val right = enumSet(int4Set(), enumSet(int3Set(), enumSet(int2Set()) ? "III") ? "IV")
      .typed(types, "V")
    val ex = in(left, right).typed(BoolT1())
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // set membership should not hold
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        // its negation holds true
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}} = {} ~~> (false)""") {
    def intSet() = enumSet().typed(types, "I")

    def int2Set() = enumSet().typed(types, "II")

    val ex = eql(enumSet(intSet()) ? "II", int2Set())
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{}}} = {{}, {{{}}} ~~> (false)""") {
    def intSet() = enumSet().typed(types, "I")

    def int2Set() = enumSet().typed(types, "II")

    def int3Set() = enumSet().typed(types, "III")

    val left = enumSet(int3Set(), enumSet(int2Set()) ? "III")
      .typed(types, "IV")
    val right = enumSet(int3Set(), enumSet(enumSet(intSet()) ? "II") ? "III")
      .typed(types, "IV")
    val ex = eql(left, right).typed(BoolT1())
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{}}} = {{}, {{}} ~~> (true)""") {
    def intSet() = enumSet().typed(types, "I")

    def int2Set() = enumSet().typed(types, "II")

    val left = enumSet(int2Set(), enumSet(intSet()) ? "II")
      .typed(types, "III")
    val right = enumSet(int2Set() ? "II", enumSet(intSet()) ? "II")
      .typed(types, "III")
    val ex = eql(left, right)
      .typed(BoolT1())
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{} = {1} \ {1} ~~> (true)""") {
    def intSet() = enumSet().typed(types, "I")

    val setOf1 = enumSet(int(1)).typed(types, "I")

    val dynEmpty =
      filter(name("t") ? "i", setOf1, bool(false))
        .typed(types, "I")

    val ex = eql(intSet(), dynEmpty).typed(BoolT1())
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        // equal
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""type incorrect { i \in {1}: FALSE } = { b \in {FALSE}: FALSE }""") {
    // This test worked in the previous versions.
    // Now we enforce type correctness, and reject this expression right after type checking.
    // Although we keep this test, it cannot originate from a well-typed TLA+ code.
    val intFilter = filter(name("i") ? "i", enumSet(int(1)) ? "I", bool(false))
      .typed(types, "I")
    val boolFilter = filter(name("b") ? "B", enumSet(bool(false)) ? "B", bool(false))
      .typed(types, "B")
    val ex = eql(intFilter ? "I", boolFilter ? "B")
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    assertThrows[MalformedTlaError] {
      rewriter.rewriteUntilDone(state)
    }
  }

  test("""~({{}, {{}}} = {{}, {{}}})""") {
    def intSet() = enumSet().typed(types, "I")

    def int2Set() = enumSet().typed(types, "II")

    val left = enumSet(int2Set(), enumSet(intSet()) ? "II")
      .typed(types, "III")
    val right = enumSet(int2Set(), enumSet(intSet()) ? "II")
      .typed(types, "III")
    val ex = not(eql(left, right) ? "b")
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
  test("""{x \in {1,2,3,4} : x % 2 = 0} ~~> {2, 4}""") {
    val set = enumSet(int(1), int(2), int(3), int(4))
      .typed(types, "I")
    val xMod2 = mod(name("x") ? "i", int(2))
      .typed(types, "i")
    val pred = eql(xMod2, int(0))
      .typed(types, "i")
    val ex = filter(name("x") ? "i", set, pred)
      .typed(types, "I")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case newSet @ NameEx(name) =>
        rewriter.push()
        assert(solverContext.sat())
      // we check actual membership in another test

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in {x \in {1,2,3,4} : x < 3}""") {
    val set = enumSet(int(1), int(2), int(3), int(4))
      .typed(types, "I")
    val pred = lt(name("x") ? "i", int(3))
      .typed(types, "b")
    val filteredSet = filter(name("x") ? "i", set, pred)
      .typed(types, "I")
    val inFilteredSet = in(int(2), filteredSet)
      .typed(types, "b")

    val state = new SymbState(inFilteredSet, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx ? "b").typed(types, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{Q \in Expand(SUBSET {1,2,3}) : ~(2 \in Q)}""") {
    val set = enumSet(1.to(3).map(int): _*).typed(types, "I")

    val predEx = not(in(int(2), name("Q") ? "I") ? "b")
      .typed(types, "b")
    val expandedPowSet = apalacheExpand(powSet(set) ? "II")
    val ex = filter(name("Q") ? "I", expandedPowSet ? "II", predEx ? "b")
      .typed(types, "II")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val inPred = in(enumSet(int(1), int(3)) ? "I", nextState.ex)
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(inPred))
    val notInPred = not(in(enumSet(int(1), int(2)).typed(types, "I"), nextState.ex) ? "b")
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(notInPred))
  }

  test("""\E X \in SUBSET {1} IN {} = {x \in X : [y \in X |-> TRUE][x]}""") {
    // regression
    val baseSet = enumSet(int(1))
      .typed(types, "I")
    val pred = appFun(funDef(bool(true), name("y") ? "i", name("X") ? "I") ? "i_to_b", name("x") ? "i")
      .typed(types, "b")
    val filteredSet = filter(name("x") ? "i", name("X") ? "II", pred ? "b")
      .typed(types, "I")
    val ex =
      apalacheSkolem(exists(name("X") ? "I", powSet(baseSet) ? "II", eql(enumSet() ? "I", filteredSet) ? "b") ? "b")
        .typed(types, "b")

    val state = new SymbState(ex, arena, Binding())
    val rewriter = new SymbStateRewriterImpl(solverContext, new TrivialTypeFinder())
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        assert(solverContext.sat())
        rewriter.push()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""\E X \in SUBSET {1, 2}: {} = {x \in X : [y \in {1} |-> TRUE][x]}""") {
    // regression
    val set1 = enumSet(int(1))
      .typed(types, "I")
    val pred = appFun(funDef(bool(true), name("y") ? "i", set1) ? "i_to_b", name("x") ? "i")
      .typed(types, "b")
    val filteredSet = filter(name("x") ? "i", name("X") ? "I", pred)
      .typed(types, "I")
    val set12 = enumSet(int(1), int(2))
      .typed(types, "I")
    val ex =
      apalacheSkolem(exists(name("X") ? "I", powSet(set12) ? "II", eql(enumSet() ? "I", filteredSet) ? "b") ? "b")
        .typed(types, "b")

    val state = new SymbState(ex, arena, Binding())
    val rewriter = new SymbStateRewriterImpl(solverContext, new TrivialTypeFinder())
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        // the new implementation just returns a default value, as in the classical TLA+ interpretation
        assert(solverContext.sat())
        // the result should be true, although some values may be undefined
        solverContext.assertGroundExpr(nextState.ex)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""3 \in {x \in {2, 3} : x % 2 = 0}""") {
    val set = enumSet(int(2), int(3))
      .typed(types, "I")
    val xMod2 = mod(name("x") ? "i", int(2))
      .typed(types, "i")
    val pred = eql(xMod2, int(0))
      .typed(types, "b")
    val filteredSet = filter(name("x") ? "i", set, pred)
      .typed(types, "I")
    val inFilteredSet = in(int(3), filteredSet)
      .typed(types, "b")

    val state = new SymbState(inFilteredSet, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx).typed(types, "b"))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{ x / 3: x \in {1,2,3,4} }""") {
    val set = enumSet(1 to 4 map int: _*)
      .typed(types, "I")
    val mapping = div(name("x") ? "i", int(3))
      .typed(types, "i")
    val mappedSet = map(mapping, name("x") ? "i", set)
      .typed(types, "I")

    val state = new SymbState(mappedSet, arena, Binding())
    val nextState = create().rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        assert(solverContext.sat())
      // membership tests are in the tests below

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""0 \in {x / 3: x \in {1,2,3,4}}""") {
    val set = enumSet(1 to 4 map int: _*)
      .typed(types, "I")
    val mapping = div(name("x") ? "i", int(3))
      .typed(types, "i")
    val mappedSet = map(mapping, name("x") ? "i", set)
      .typed(types, "I")
    val inMappedSet = in(int(0), mappedSet)
      .typed(types, "b")

    val state = new SymbState(inMappedSet, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx ? "b").typed(types, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in {x / 3: x \in {1,2,3,4}}""") {
    val set = enumSet(1 to 4 map int: _*)
      .typed(types, "I")
    val mapping = div(name("x") ? "i", int(3))
      .typed(types, "i")
    val mappedSet = map(mapping, name("x") ? "i", set)
      .typed(types, "I")
    val inMappedSet = in(int(2), mappedSet)
      .typed(types, "b")

    val state = new SymbState(inMappedSet, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx ? "b").typed(types, "b"))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // type inference would reject this
  test("""error: {x: x \in Int}""") {
    val set = intSet().typed(types, "I")
    val mapSet = map(name("x") ? "i", name("x") ? "i", set)
      .typed(types, "I")

    val state = new SymbState(mapSet, arena, Binding())
    val rewriter = create()
    assertThrows[TlaInputError](rewriter.rewriteUntilDone(state))
  }

  test("""<<2, true>> \in {<<x, y>>: x \in {1,2,3}, y \in {FALSE, TRUE}}""") {
    val set123 = enumSet(1 to 3 map int: _*)
      .typed(types, "I")
    val setBool = enumSet(bool(false), bool(true))
      .typed(types, "B")
    val mapping = tuple(name("x") ? "i", name("y") ? "b")
      .typed(types, "ib")
    val mappedSet = map(mapping, name("x") ? "i", set123, name("y") ? "b", setBool)
      .typed(types, "IB")
    val inMappedSet = in(tuple(int(2), bool(true)) ? "ib", mappedSet)
      .typed(types, "b")

    val state = new SymbState(inMappedSet, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx ? "b").typed(types, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""<<TRUE>> \in {<<y>>: x \in {1,2} \ {2}, y \in {FALSE, TRUE}}""") {
    // this expression tests regressions in cached expressions
    // we express {1, 2} \ {2} as a filter, as set difference is not in KerA+
    val set12minus2 = filter(name("z") ? "i", enumSet(int(1), int(2)) ? "I", eql(name("z") ? "i", int(1)) ? "b")
      .typed(types, "I")
    val setBool = enumSet(bool(false), bool(true))
      .typed(types, "B")
    val mapping = tuple(name("y") ? "b")
      .typed(types + ("(b)" -> TupT1(BoolT1())), "(b)")
    val mappedSet = map(mapping, name("x") ? "i", set12minus2 ? "I", name("y") ? "b", setBool)
      .typed(types + ("(B)" -> SetT1(TupT1(BoolT1()))), "(B)")
    val inMappedSet = in(tuple(bool(true)).typed(TupT1(BoolT1())), mappedSet)
      .typed(BoolT1())

    val state = new SymbState(inMappedSet, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx ? "b").typed(types, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // Regression for the issue 365: https://github.com/informalsystems/apalache/issues/365
  test("""MAP: \E S \in SUBSET { [a: "a", b: 1], [a: "a", b: 2] }:  "a" \in { r.a: r \in S }""") {
    // this test reveals a deep bug in the encoding: SUBSET {[a: 1, b: 1], [a: 1, b: 2]} produces a powerset,
    // whose elements are sets that refer to the same cells,
    // namely the cells for the records [a: 1, b: 1] and [a: 1, b: 2].
    // If one record is included in a subset, but the other is not, then the map rule produced a contradicting constraint
    // for the element "a": it must be in the resulting set, and at the same time it must not be in the resulting set.
    val recTypes =
      Map("b" -> BoolT1(), "s" -> StrT1(), "S" -> SetT1(StrT1()), "r" -> RecT1("a" -> StrT1(), "b" -> IntT1()),
          "R" -> SetT1(RecT1("a" -> StrT1(), "b" -> IntT1())),
          "RR" -> SetT1(SetT1(RecT1("a" -> StrT1(), "b" -> IntT1()))))
    val rec1 = enumFun(str("a"), str("a"), str("b"), int(1))
      .typed(recTypes, "r")
    val rec2 = enumFun(str("a"), str("a"), str("b"), int(2))
      .typed(recTypes, "r")
    val base = enumSet(rec1, rec2)
      .typed(recTypes, "R")
    val powerset = powSet(base)
      .typed(recTypes, "RR")
    val mapped = map(appFun(name("r") ? "r", str("a")) ? "s", name("r") ? "r", name("S") ? "R")
      .typed(recTypes, "S")
    val mem = in(str("a"), mapped)
      .typed(BoolT1())
    val existsForm = apalacheSkolem(exists(name("S") ? "R", powerset ? "RR", mem) ? "b")
      .typed(recTypes, "b")

    // the following test goes through without a need for a fix
    val rewriter = create()
    val state = new SymbState(existsForm, arena, Binding())
    assumeTlaEx(rewriter, state)

    // the following test captures the core of the functional test in `test/tla/Fix365_ExistsSubset3.tla`,
    // which needed a fix
    // \E S \in SUBSET { [a: "a", b: 1], [a: "a", b: 2] }:  "a" \in { r.a: r \in S } /\ \A x \in S: x.b = 2
    val forallForm =
      forall(name("x") ? "r", name("S") ? "R", eql(appFun(name("x") ? "r", str("b")) ? "b", int(2)) ? "b")
        .typed(recTypes, "b")
    val existsForm2 = apalacheSkolem(exists(name("S") ? "R", powerset, and(mem, forallForm) ? "b") ? "b")
      .typed(recTypes, "b")

    // reset the solver and arena
    solverContext = new PreproSolverContext(new Z3SolverContext(SolverConfig.default.copy(debug = true)))
    arena = Arena.create(solverContext)
    val rewriter2 = create()
    val state2 = new SymbState(existsForm2, arena, Binding())
    assumeTlaEx(rewriter2, state2)
  }

  test("""{1, 3} \cup {3, 4} = {1, 3, 4}""") {
    val left = enumSet(int(1), int(3))
      .typed(types, "I")
    val right = enumSet(int(3), int(4))
      .typed(types, "I")
    val expected = enumSet(int(1), int(3), int(4))
      .typed(types, "I")
    val cupSet = cup(left, right)
      .typed(types, "I")
    val eqExpected = eql(cupSet, expected)
      .typed(types, "b")

    val state = new SymbState(eqExpected, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(solverContext.sat())
        // check equality
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 2} \subseteq {1, 2, 3} ~~> (true)""") {
    val left = enumSet(int(1), int(2))
      .typed(types, "I")
    val right = enumSet(int(1), int(2), int(3))
      .typed(types, "I")
    val ex = subseteq(left, right)
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 2, 3} \subseteq {1, 2, 3} ~~> (true)""") {
    val right = enumSet(int(1), int(2), int(3))
      .typed(types, "I")
    val ex = subseteq(right, right)
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{} \subseteq {1, 2, 3} ~~> (true)""") {
    val right = enumSet(int(1), int(2), int(3))
      .typed(types, "I")
    // an empty set requires a type annotation
    val ex = subseteq(enumSet() ? "I", right)
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 4} \subseteq {1, 2, 3} ~~> (false)""") {
    val left = enumSet(int(1), int(4))
      .typed(types, "I")
    val right = enumSet(int(1), int(2), int(3))
      .typed(types, "I")
    val ex = subseteq(left, right)
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(rewriter, nextState)
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(types, "b"))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""UNION {{1, 2}, {2,3}} = {1, 2, 3}""") {
    val setOf12 = enumSet(int(1), int(2))
      .typed(types, "I")
    val setOf23 = enumSet(int(3), int(2))
      .typed(types, "I")
    val setOf123 = enumSet(int(1), int(2), int(3))
      .typed(types, "I")
    // This may seem weird, but since we don't know the type of {},
    // it should be equal to the empty set of ints.
    val eq = eql(union(enumSet(setOf12, setOf23) ? "II") ? "I", setOf123)
      .typed(types, "b")
    val rewriter = create()
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

}
