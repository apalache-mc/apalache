package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import at.forsyte.apalache.tla.bmcmt.smt.{PreproSolverContext, SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.pp.TlaInputError
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterSet extends RewriterBase {
  private val parser = DefaultType1Parser
  private val intT = parser("Int")
  private val intSetT = parser("Set(Int)")
  private val int2SetT = parser("Set(Set(Int))")
  private val int3SetT = parser("Set(Set(Set(Int)))")
  private val int4SetT = parser("Set(Set(Set(Set(Int))))")
  private val int5SetT = parser("Set(Set(Set(Set(Set(Int)))))")
  private val boolT = parser("Bool")
  private val boolSetT = parser("Set(Bool)")
  private val intToBoolT = parser("Int -> Bool")
  private val intBoolT = parser("<<Int, Bool>>")
  private val intBoolSetT = parser("Set(<<Int, Bool>>)")

  test("""{ x, y, z } ~~> c_set""") {
    val ex = enumSet(name("x") as intT, name("y") as boolT, name("z") as boolT) as boolSetT
    val binding = Binding("x" -> arena.cellFalse(), "y" -> arena.cellTrue(), "z" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case set @ NameEx(_) =>
            val falseInSet = in(arena.cellFalse().toNameEx as boolT, set as boolSetT) as boolT
            solverContext.assertGroundExpr(falseInSet)
            assert(solverContext.sat())
            val notTrueInSet = not(in(arena.cellTrue().toNameEx as boolT, set as boolSetT) as boolT) as boolT
            solverContext.assertGroundExpr(notTrueInSet)
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 3, 5} ~~> c_set""") {
    val ex = enumSet(int(1), int(3), int(5)) as intSetT
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
    val ex = in(enumSet() as intSetT, enumSet() as int2SetT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val nextState = create().rewriteUntilDone(state)
    assert(nextState.arena.cellFalse().toNameEx == nextState.ex)
  }

  test("""3 \in {1, 3, 5}""") {
    val ex = in(int(3), enumSet(int(1), int(3), int(5)) as intSetT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{3} \in {{1}, {3}, {5}}""") {
    val ex = in(enumSet(int(3)) as intSetT,
        enumSet(enumSet(int(1)) as intSetT, enumSet(int(3)) as intSetT,
            enumSet(int(5)) as intSetT) as int2SetT) as boolT

    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in {1, 3, 5}""") {
    val ex = in(int(2), enumSet(int(1), int(3), int(5)) as intSetT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in Int""") {
    val ex = in(int(2), intSet() as intSetT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  test("""2 \in Nat""") {
    val ex = in(int(2), natSet() as intSetT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  test("""-1 \in Nat""") {
    val ex = in(int(-1), natSet() as intSetT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState.setRex(not(nextState.ex as boolT) as boolT))
  }

  test("""~({} \in {})""") {
    val ex = not(in(enumSet() as intSetT, enumSet() as int2SetT) as boolT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.push()
    solverContext.assertGroundExpr(not(nextState.ex as boolT) as boolT)
    assert(!solverContext.sat())
    solverContext.pop()
  }

  test("""FALSE \in {FALSE, TRUE}""") {
    val ex =
      in(bool(false), enumSet(bool(false), bool(true)) as boolSetT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx @ NameEx(name) =>
            rewriter.push()
            solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
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
      not(in(bool(false), enumSet(bool(false), bool(true)) as boolSetT) as boolT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteUntilDone(state).ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
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
      in(cell.toNameEx as boolT, enumSet(bool(true), bool(true)) as boolSetT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx @ NameEx(name) =>
            rewriter.push()
            // cell = \TRUE
            solverContext.assertGroundExpr(eql(arena.cellTrue().toNameEx as boolT, cell.toNameEx as boolT) as boolT)
            // and membership holds true
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())
            rewriter.pop()
            // another query
            // cell = \FALSE
            solverContext.assertGroundExpr(eql(arena.cellFalse().toNameEx as boolT, cell.toNameEx as boolT) as boolT)
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
    val ex = in(int(1), enumSet(int(1)) as intSetT) as boolT

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
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
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
      not(in(cell.toNameEx as boolT, enumSet(bool(true), bool(true)) as boolSetT) as boolT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteUntilDone(state).ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        // cell = TRUE
        solverContext.assertGroundExpr(eql(arena.cellTrue().toNameEx as boolT, cell.toNameEx as boolT) as boolT)
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        // another query
        // cell = \FALSE
        solverContext.assertGroundExpr(eql(arena.cellFalse().toNameEx as boolT, cell.toNameEx as boolT) as boolT)
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        // no contradiction here
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{}, {}}} \in {{}, {{}, {{}, {}}}}""") {
    def intSet() = enumSet() as intSetT

    def int2Set() = enumSet() as int2SetT

    def int3Set() = enumSet() as int3SetT

    val left = enumSet(int2Set(), enumSet(intSet(), intSet()) as int2SetT) as int3SetT
    val right =
      enumSet(int3Set(),
          enumSet(int2Set() as int2SetT, enumSet(intSet(), intSet()) as int2SetT) as int3SetT) as int4SetT
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
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{{}}}} \in {{}, {{}, {{}}}""") {
    def intSet() = enumSet() as intSetT

    def int2Set() = enumSet() as int2SetT

    def int3Set() = enumSet() as int3SetT

    def int4Set() = enumSet() as int4SetT

    val left = enumSet(int3Set(), enumSet(enumSet(intSet()) as int2SetT) as int3SetT) as int4SetT
    val right = enumSet(int4Set(), enumSet(int3Set(), enumSet(int2Set()) as int3SetT) as int4SetT) as int5SetT
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
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}} = {} ~~> (false)""") {
    def intSet() = enumSet() as intSetT

    def int2Set() = enumSet() as int2SetT

    val ex = eql(enumSet(intSet()) as int2SetT, int2Set()) as boolT
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
    def intSet() = enumSet() as intSetT

    def int2Set() = enumSet() as int2SetT

    def int3Set() = enumSet() as int3SetT

    val left = enumSet(int3Set(), enumSet(int2Set()) as int3SetT) as int4SetT
    val right = enumSet(int3Set(), enumSet(enumSet(intSet()) as int2SetT) as int3SetT) as int4SetT
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
    def intSet() = enumSet() as intSetT

    def int2Set() = enumSet() as int2SetT

    val left = enumSet(int2Set(), enumSet(intSet()) as int2SetT) as int3SetT
    val right = enumSet(int2Set() as int2SetT, enumSet(intSet()) as int2SetT) as int3SetT
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
    def intSet() = enumSet() as intSetT

    val setOf1 = enumSet(int(1)) as intSetT

    val dynEmpty =
      filter(name("t") as intT, setOf1, bool(false)) as intSetT

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
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""type incorrect { i \in {1}: FALSE } = { b \in {FALSE}: FALSE }""") {
    // This test worked in the previous versions.
    // Now we enforce type correctness, and reject this expression right after type checking.
    // Although we keep this test, it cannot originate from a well-typed TLA+ code.
    val intFilter = filter(name("i") as intT, enumSet(int(1)) as intSetT, bool(false)) as intSetT
    val boolFilter = filter(name("b") as boolSetT, enumSet(bool(false)) as boolSetT, bool(false)) as boolSetT
    val ex = eql(intFilter as intSetT, boolFilter as boolSetT) as boolT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    assertThrows[MalformedTlaError] {
      rewriter.rewriteUntilDone(state)
    }
  }

  test("""~({{}, {{}}} = {{}, {{}}})""") {
    def intSet() = enumSet() as intSetT

    def int2Set() = enumSet() as int2SetT

    val left = enumSet(int2Set(), enumSet(intSet()) as int2SetT) as int3SetT
    val right = enumSet(int2Set(), enumSet(intSet()) as int2SetT) as int3SetT
    val ex = not(eql(left, right) as boolT) as boolT
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
    val set = enumSet(int(1), int(2), int(3), int(4)) as intSetT
    val xMod2 = mod(name("x") as intT, int(2)) as intT
    val pred = eql(xMod2, int(0)) as intT
    val ex = filter(name("x") as intT, set, pred) as intSetT
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
    val set = enumSet(int(1), int(2), int(3), int(4)) as intSetT
    val pred = lt(name("x") as intT, int(3)) as boolT
    val filteredSet = filter(name("x") as intT, set, pred) as intSetT
    val inFilteredSet = in(int(2), filteredSet) as boolT

    val state = new SymbState(inFilteredSet, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx as boolT) as boolT)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{Q \in Expand(SUBSET {1,2,3}) : ~(2 \in Q)}""") {
    val set = enumSet(1.to(3).map(int): _*) as intSetT

    val predEx = not(in(int(2), name("Q") as intSetT) as boolT) as boolT
    val expandedPowSet = apalacheExpand(powSet(set) as int2SetT)
    val ex = filter(name("Q") as intSetT, expandedPowSet as int2SetT, predEx as boolT) as int2SetT
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val inPred = in(enumSet(int(1), int(3)) as intSetT, nextState.ex) as boolT
    assertTlaExAndRestore(rewriter, nextState.setRex(inPred))
    val notInPred = not(in(enumSet(int(1), int(2)) as intSetT, nextState.ex) as boolT) as boolT
    assertTlaExAndRestore(rewriter, nextState.setRex(notInPred))
  }

  test("""\E X \in SUBSET {1} IN {} = {x \in X : [y \in X |-> TRUE][x]}""") {
    // regression
    val baseSet = enumSet(int(1)) as intSetT
    val pred =
      appFun(funDef(bool(true), name("y") as intT, name("X") as intSetT) as intToBoolT, name("x") as intT) as boolT
    val filteredSet = filter(name("x") as intT, name("X") as int2SetT, pred as boolT) as intSetT
    val ex =
      apalacheSkolem(exists(name("X") as intSetT, powSet(baseSet) as int2SetT,
              eql(enumSet() as intSetT, filteredSet) as boolT) as boolT) as boolT

    val state = new SymbState(ex, arena, Binding())
    val rewriter = new SymbStateRewriterImpl(solverContext)
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
    val set1 = enumSet(int(1)) as intSetT
    val pred = appFun(funDef(bool(true), name("y") as intT, set1) as intToBoolT, name("x") as intT) as boolT
    val filteredSet = filter(name("x") as intT, name("X") as intSetT, pred) as intSetT
    val set12 = enumSet(int(1), int(2)) as intSetT
    val ex =
      apalacheSkolem(exists(name("X") as intSetT, powSet(set12) as int2SetT,
              eql(enumSet() as intSetT, filteredSet) as boolT) as boolT) as boolT

    val state = new SymbState(ex, arena, Binding())
    val rewriter = new SymbStateRewriterImpl(solverContext)
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
    val set = enumSet(int(2), int(3)) as intSetT
    val xMod2 = mod(name("x") as intT, int(2)) as intT
    val pred = eql(xMod2, int(0)) as boolT
    val filteredSet = filter(name("x") as intT, set, pred) as intSetT
    val inFilteredSet = in(int(3), filteredSet) as boolT

    val state = new SymbState(inFilteredSet, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx) as boolT)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{ x / 3: x \in {1,2,3,4} }""") {
    val set = enumSet(1 to 4 map int: _*) as intSetT
    val mapping = div(name("x") as intT, int(3)) as intT
    val mappedSet = map(mapping, name("x") as intT, set) as intSetT

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
    val set = enumSet(1 to 4 map int: _*) as intSetT
    val mapping = div(name("x") as intT, int(3)) as intT
    val mappedSet = map(mapping, name("x") as intT, set) as intSetT
    val inMappedSet = in(int(0), mappedSet) as boolT

    val state = new SymbState(inMappedSet, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx as boolT) as boolT)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in {x / 3: x \in {1,2,3,4}}""") {
    val set = enumSet(1 to 4 map int: _*) as intSetT
    val mapping = div(name("x") as intT, int(3)) as intT
    val mappedSet = map(mapping, name("x") as intT, set) as intSetT
    val inMappedSet = in(int(2), mappedSet) as boolT

    val state = new SymbState(inMappedSet, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx as boolT) as boolT)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // type inference would reject this
  test("""error: {x: x \in Int}""") {
    val set = intSet() as intSetT
    val mapSet = map(name("x") as intT, name("x") as intT, set) as intSetT

    val state = new SymbState(mapSet, arena, Binding())
    val rewriter = create()
    assertThrows[TlaInputError](rewriter.rewriteUntilDone(state))
  }

  test("""<<2, true>> \in {<<x, y>>: x \in {1,2,3}, y \in {FALSE, TRUE}}""") {
    val set123 = enumSet(1 to 3 map int: _*) as intSetT
    val setBool = enumSet(bool(false), bool(true)) as boolSetT
    val mapping = tuple(name("x") as intT, name("y") as boolT) as intBoolT
    val mappedSet = map(mapping, name("x") as intT, set123, name("y") as boolT, setBool) as intBoolSetT
    val inMappedSet = in(tuple(int(2), bool(true)) as intBoolT, mappedSet) as boolT

    val state = new SymbState(inMappedSet, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx as boolT) as boolT)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""<<TRUE>> \in {<<y>>: x \in {1,2} \ {2}, y \in {FALSE, TRUE}}""") {
    // this expression tests regressions in cached expressions
    // we express {1, 2} \ {2} as a filter, as set difference is not in KerA+
    val set12minus2 =
      filter(name("z") as intT, enumSet(int(1), int(2)) as intSetT, eql(name("z") as intT, int(1)) as boolT) as intSetT
    val setBool = enumSet(bool(false), bool(true)) as boolSetT
    val mapping = tuple(name("y") as boolT) as parser("<<Bool>>")
    val mappedSet =
      map(mapping, name("x") as intT, set12minus2 as intSetT, name("y") as boolT, setBool) as parser("Set(<<Bool>>)")
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
        solverContext.assertGroundExpr(not(membershipEx as boolT) as boolT)
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
    val recT = parser("[a: Str, b: Int]")
    val recSetT = parser("Set([a: Str, b: Int])")
    val rec2SetT = parser("Set(Set([a: Str, b: Int]))")
    val strT = parser("Str")
    val strSetT = parser("Set(Str)")
    val rec1 = enumFun(str("a"), str("a"), str("b"), int(1)) as recT
    val rec2 = enumFun(str("a"), str("a"), str("b"), int(2)) as recT
    val base = enumSet(rec1, rec2) as recSetT
    val powerset = powSet(base) as rec2SetT
    val mapped =
      map(appFun(name("r") as recT, str("a")) as strT, name("r") as recT, name("S") as recSetT) as strSetT
    val mem = in(str("a"), mapped) as boolT
    val existsForm = apalacheSkolem(exists(name("S") as recSetT, powerset as rec2SetT, mem) as boolT) as boolT

    // the following test goes through without a need for a fix
    val rewriter = create()
    val state = new SymbState(existsForm, arena, Binding())
    assumeTlaEx(rewriter, state)

    // the following test captures the core of the functional test in `test/tla/Fix365_ExistsSubset3.tla`,
    // which needed a fix
    // \E S \in SUBSET { [a: "a", b: 1], [a: "a", b: 2] }:  "a" \in { r.a: r \in S } /\ \A x \in S: x.b = 2
    val forallForm =
      forall(name("x") as recT, name("S") as recSetT,
          eql(appFun(name("x") as recT, str("b")) as boolT, int(2)) as boolT) as boolT
    val existsForm2 =
      apalacheSkolem(exists(name("S") as recSetT, powerset, and(mem, forallForm) as boolT) as boolT) as boolT

    // reset the solver and arena
    solverContext = new PreproSolverContext(new Z3SolverContext(SolverConfig.default.copy(debug = true)))
    arena = Arena.create(solverContext)
    val rewriter2 = create()
    val state2 = new SymbState(existsForm2, arena, Binding())
    assumeTlaEx(rewriter2, state2)
  }

  test("""{1, 3} \cup {3, 4} = {1, 3, 4}""") {
    val left = enumSet(int(1), int(3)) as intSetT
    val right = enumSet(int(3), int(4)) as intSetT
    val expected = enumSet(int(1), int(3), int(4)) as intSetT
    val cupSet = cup(left, right) as intSetT
    val eqExpected = eql(cupSet, expected) as boolT

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
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 2} \subseteq {1, 2, 3} ~~> (true)""") {
    val left = enumSet(int(1), int(2)) as intSetT
    val right = enumSet(int(1), int(2), int(3)) as intSetT
    val ex = subseteq(left, right) as boolT
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
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 2, 3} \subseteq {1, 2, 3} ~~> (true)""") {
    val right = enumSet(int(1), int(2), int(3)) as intSetT
    val ex = subseteq(right, right) as boolT
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
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{} \subseteq {1, 2, 3} ~~> (true)""") {
    val right = enumSet(int(1), int(2), int(3)) as intSetT
    // an empty set requires a type annotation
    val ex = subseteq(enumSet() as intSetT, right) as boolT
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
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 4} \subseteq {1, 2, 3} ~~> (false)""") {
    val left = enumSet(int(1), int(4)) as intSetT
    val right = enumSet(int(1), int(2), int(3)) as intSetT
    val ex = subseteq(left, right) as boolT
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
        solverContext.assertGroundExpr(not(predEx as boolT) as boolT)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""UNION {{1, 2}, {2,3}} = {1, 2, 3}""") {
    val setOf12 = enumSet(int(1), int(2)) as intSetT
    val setOf23 = enumSet(int(3), int(2)) as intSetT
    val setOf123 = enumSet(int(1), int(2), int(3)) as intSetT
    // This may seem weird, but since we don't know the type of {},
    // it should be equal to the empty set of ints.
    val eq = eql(union(enumSet(setOf12, setOf23) as int2SetT) as intSetT, setOf123) as boolT
    val rewriter = create()
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

}
