package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.analyses.FreeExistentialsStoreImpl
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.plugins.Identifier
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaInt, TlaTrue}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterSet extends RewriterBase with TestingPredefs {
  private def emptySetWithType(elemT: CellT): TlaEx =
    tla.withType(tla.enumSet(), AnnotationParser.toTla(FinSetT(elemT)))


  test("""SE-SET-CTOR[1-2]: {x, y, z} ~~> c_set""") {
    val ex = OperEx(TlaSetOper.enumSet, NameEx("x"), NameEx("y"), NameEx("z"))
    val binding = new Binding + ("x" -> arena.cellFalse()) +
      ("y" -> arena.cellTrue()) + ("z" -> arena.cellFalse())
    val state = new SymbState(ex, CellTheory(), arena, binding)
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case set@NameEx(name) =>
            assert(CellTheory().hasConst(name))
            solverContext.assertGroundExpr(OperEx(TlaSetOper.in, arena.cellFalse().toNameEx, set))
            assert(solverContext.sat())
            solverContext.assertGroundExpr(OperEx(TlaBoolOper.not,
              OperEx(TlaSetOper.in, arena.cellTrue().toNameEx, set)))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-CTOR[1-2]: {1, 3, 5} ~~> c_set""") {
    val ex = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(1)), ValEx(TlaInt(3)), ValEx(TlaInt(5)))
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case set@NameEx(name) =>
            assert(CellTheory().hasConst(name))
            assert(solverContext.sat())
          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN1: {} \in {} ~~> $B$0""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)
    val ex = OperEx(TlaSetOper.in,
      emptySetWithType(IntT()),
      emptySetWithType(FinSetT(IntT())))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val nextState = create().rewriteUntilDone(state)
    assert(NameEx(SolverContext.falseConst) == nextState.ex)
  }

  test("""SE-SET-IN1: 3 \in {1, 3, 5} ~~> $B$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ex = OperEx(TlaSetOper.in,
      ValEx(TlaInt(3)),
      mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(3)), ValEx(TlaInt(5))))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN1: {3} \in {{1}, {3}, {5}} ~~> $B$k""") {
    val ex = tla.in(tla.enumSet(tla.int(3)),
      tla.enumSet(tla.enumSet(tla.int(1)), tla.enumSet(tla.int(3)), tla.enumSet(tla.int(5))))

    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN1: 2 \in {1, 3, 5} ~~> $B$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ex = OperEx(TlaSetOper.in,
      ValEx(TlaInt(2)),
      mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(3)), ValEx(TlaInt(5))))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""type inference 3 \in {{1}, {3}, {5}}""") {
    // this test worked in the previous versions, but now it just reports a type inference error
    val ex = tla.in(tla.int(3),
      tla.enumSet(tla.enumSet(tla.int(1)), tla.enumSet(tla.int(3)), tla.enumSet(tla.int(5))))

    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    assertThrows[TypeInferenceError] {
      rewriter.rewriteUntilDone(state)
    }
  }

  test("""SE-SET-NOTIN1: {} \notin {} ~~> $B$1""") {
    val ex = OperEx(TlaSetOper.notin,
      emptySetWithType(FinSetT(IntT())),
      emptySetWithType(FinSetT(FinSetT(IntT()))))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assert(!solverContext.sat())
    solverContext.pop()
  }

  test("""SE-SET-IN2: \FALSE \in {\FALSE, \TRUE} ~~> b_new""") {
    val ex =
      OperEx(TlaSetOper.in,
        ValEx(TlaFalse),
        OperEx(TlaSetOper.enumSet, ValEx(TlaFalse), ValEx(TlaTrue)))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx@NameEx(name) =>
            assert(BoolTheory().hasConst(name))
            rewriter.push()
            solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
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

  test("""SE-SET-NOTIN1: \FALSE \notin {\FALSE, \TRUE} ~~> b_new""") {
    val ex =
      OperEx(TlaSetOper.notin,
        ValEx(TlaFalse),
        OperEx(TlaSetOper.enumSet, ValEx(TlaFalse), ValEx(TlaTrue)))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    rewriter.rewriteUntilDone(state).ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN3: c_i: Bool \in {\TRUE, \TRUE} ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val cell = arena.topCell
    val ex =
      OperEx(TlaSetOper.in,
        cell.toNameEx,
        OperEx(TlaSetOper.enumSet, ValEx(TlaTrue), ValEx(TlaTrue)))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx@NameEx(name) =>
            assert(BoolTheory().hasConst(name))
            rewriter.push()
            // cell = \TRUE
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, cell.toNameEx))
            // and membership holds true
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())
            rewriter.pop()
            // another query
            // cell = \FALSE
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, arena.cellFalse().toNameEx, cell.toNameEx))
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

  test("""SE-SET-IN1 (shortcut): 1 \in {1} ~~> $B$k""") {
    // there is a special shortcut rule for singleton sets, which had a bug
    val ex = tla.in(tla.int(1), tla.enumSet(tla.int(1)))

    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        nextState.arena.appendCell(IntT()) // the buggy rule implementation triggered an error here
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())
        rewriter.pop()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-NOTIN1: c_i: Bool \notin {\TRUE, \TRUE} ~~> c_pred""") {
    arena = arena.appendCell(BoolT())
    val cell = arena.topCell
    val ex =
      OperEx(TlaSetOper.notin,
        cell.toNameEx,
        OperEx(TlaSetOper.enumSet, ValEx(TlaTrue), ValEx(TlaTrue)))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    rewriter.rewriteUntilDone(state).ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        // cell = \TRUE
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, cell.toNameEx))
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        // another query
        // cell = \FALSE
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, arena.cellFalse().toNameEx, cell.toNameEx))
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        // no contradiction here
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN3: {{}, {{}, {}}} \in {{}, {{}, {{}, {}}}} ~~> b_new""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)
    def intSet() = emptySetWithType(IntT())
    def int2Set() = emptySetWithType(FinSetT(IntT()))
    def int3Set() = emptySetWithType(FinSetT(FinSetT(IntT())))

    val left = mkSet(int2Set(), mkSet(intSet(), intSet()))
    val right = mkSet(int3Set(), mkSet(int2Set(), mkSet(intSet(), intSet())))
    val ex = OperEx(TlaSetOper.in, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        // another query
        // and membership does not hold
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN3: {{}, {{{}}}} \in {{}, {{}, {{}}} ~~> b_new""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)
    def intSet() = emptySetWithType(IntT())
    def int2Set() = emptySetWithType(FinSetT(IntT()))
    def int3Set() = emptySetWithType(FinSetT(FinSetT(IntT())))
    def int4Set() = emptySetWithType(FinSetT(FinSetT(FinSetT(IntT()))))

    val left = mkSet(int3Set(), mkSet(mkSet(intSet())))
    val right = mkSet(int4Set(), mkSet(int3Set(), mkSet(int2Set())))
    val ex = OperEx(TlaSetOper.in, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        // set membership should not hold
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        // its negation holds true
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-EQ1: {{}} = {} ~~> $B$... (false)""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)
    def intSet() = emptySetWithType(IntT())           // empty sets need types
    def int2Set() = emptySetWithType(FinSetT(IntT())) // empty sets need types

    val ex = tla.eql(tla.enumSet(intSet()), int2Set())
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-EQ1: {{}, {{}}} = {{}, {{{}}} ~~> $B$... (false)""") {
    def intSet() = emptySetWithType(IntT())
    def int2Set() = emptySetWithType(FinSetT(IntT()))
    def int3Set() = emptySetWithType(FinSetT(FinSetT(IntT())))

    val left = tla.enumSet(int3Set(), tla.enumSet(int2Set()))
    val right = tla.enumSet(int3Set(), tla.enumSet(tla.enumSet(intSet())))
    val ex = OperEx(TlaOper.eq, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-EQ1: {{}, {{}}} = {{}, {{}} ~~> $B$... (true)""") {
    def intSet() = emptySetWithType(IntT())
    def int2Set() = emptySetWithType(FinSetT(IntT()))

    val left = tla.enumSet(int2Set(), tla.enumSet(intSet()))
    val right = tla.enumSet(int2Set(), tla.enumSet(intSet()))
    val ex = OperEx(TlaOper.eq, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-EQ1: {} = {1} \ {1} ~~> $B$... (true)""") {
    def intSet() = emptySetWithType(IntT())
    val setOf1 = tla.enumSet(tla.int(1))
    val ex = OperEx(TlaOper.eq, intSet(), tla.setminus(setOf1, setOf1))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        // equal
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(predEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""type incorrect {1} \ {1} = {FALSE} \ {FALSE}""") {
    // This test worked in the previous versions.
    // Now we enforce type correctness, and reject this expression right after type checking.
    val setOfOne = tla.enumSet(tla.int(1))
    val setOfFalse = tla.enumSet(tla.bool(false))
    val ex = OperEx(TlaOper.eq,
      tla.setminus(setOfFalse, setOfFalse),
      tla.setminus(setOfOne, setOfOne))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    assertThrows[TypeInferenceError] {
      rewriter.rewriteUntilDone(state)
    }
  }

  test("""SE-SET-NE1: {{}, {{}}} != {{}, {{}}} ~~> $B$... (false)""") {
    def intSet() = emptySetWithType(IntT())
    def int2Set() = emptySetWithType(FinSetT(IntT()))

    val left = tla.enumSet(int2Set(), tla.enumSet(intSet()))
    val right = tla.enumSet(int2Set(), tla.enumSet(intSet()))
    val ex = OperEx(TlaOper.ne, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
  test("""SE-SET-FILTER[1-2]: {x \in {1,2,3,4} : x % 2 = 0} ~~> {2, 4}""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val xMod2 = OperEx(TlaArithOper.mod, NameEx("x"), ValEx(TlaInt(2)))
    val filter = OperEx(TlaOper.eq, xMod2, ValEx(TlaInt(0)))
    val ex = OperEx(TlaSetOper.filter, NameEx("x"), set, filter)
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case newSet@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        rewriter.push()
        assert(solverContext.sat())
      // we check actual membership in another test

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-FILTER[1-2]: 2 \in {x \in {1,2,3,4} : x < 3} ~~> $B$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val filter = tla.lt(tla.name("x"), tla.int(3))
    val filteredSet = OperEx(TlaSetOper.filter, NameEx("x"), set, filter)
    val inFilteredSet = OperEx(TlaSetOper.in, ValEx(TlaInt(2)), filteredSet)

    val state = new SymbState(inFilteredSet, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, membershipEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // until the real type inference is implemented
  ignore("""SE-SET-FILTER[1-2]: LET X = {1, 2} \cap {2} IN {} = {x \in X : [y \in X |-> TRUE][x]} ~~> $B$k""") {
    // regression
    val filter = tla.appFun(tla.funDef(tla.bool(true), "y", "Oper:X"), "x")
    val filteredSet = tla.filter("x", "Oper:X", filter)
    val ex = tla.letIn(tla.eql(tla.enumSet(), filteredSet),
      tla.declOp("X", tla.cap(tla.enumSet(1, 2), tla.enumSet(2))))

    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriterImpl(solverContext, new TrivialTypeFinder())
    val fex = new FreeExistentialsStoreImpl()
    Identifier.identify(ex) // XXX: should not be here
    fex.store = fex.store + ex.ID
    rewriter.freeExistentialsStore = fex
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        val failPreds = nextState.arena.findCellsByType(FailPredT())
        val failureOccurs = tla.or(failPreds.map(_.toNameEx): _*)
        solverContext.assertGroundExpr(failureOccurs)
        assert(!solverContext.sat()) // no failure should be possible

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-FILTER[1-2]: \E SUBSET X {1} IN {} = {x \in X : [y \in X |-> TRUE][x]} ~~> $B$k""") {
    // regression
    val baseSet = tla.enumSet(1)
    val filter = tla.appFun(tla.funDef(tla.bool(true), "y", "X"), "x")
    val filteredSet = tla.filter("x", "X", filter)
    val ex = tla.exists("X", tla.powSet(baseSet), tla.eql(tla.enumSet(), filteredSet))

    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriterImpl(solverContext, new TrivialTypeFinder())
    val fex = new FreeExistentialsStoreImpl()
    Identifier.identify(ex) // XXX: should not be here
    fex.store = fex.store + ex.ID
    rewriter.freeExistentialsStore = fex
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(solverContext.sat())
        rewriter.push()
        val failPreds = nextState.arena.findCellsByType(FailPredT())
        val failureOccurs = tla.or(failPreds.map(_.toNameEx): _*)
        solverContext.assertGroundExpr(failureOccurs)
        assert(!solverContext.sat()) // no failure should be possible

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-FILTER[1-2]: \E X \in SUBSET {1, 2}: {} = {x \in X : [y \in {1} |-> TRUE][x]} ~~> $B$k""") {
    // regression
    val baseSet = tla.enumSet(1)
    val filter = tla.appFun(tla.funDef(tla.bool(true), "y", tla.enumSet(1)), "x")
    val filteredSet = tla.filter("x", "X", filter)
    val ex = tla.exists("X", tla.powSet(tla.enumSet(1, 2)), tla.eql(tla.enumSet(), filteredSet))

    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriterImpl(solverContext, new TrivialTypeFinder())
    val fex = new FreeExistentialsStoreImpl()
    Identifier.identify(ex) // XXX: should not be here
    fex.store = fex.store + ex.ID
    rewriter.freeExistentialsStore = fex
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        // the new implementation just returns a default value, as in the classical TLA+ interpretation
        assert(solverContext.sat())
        // the result should be true, although some values may be undefined
        solverContext.assertGroundExpr(nextState.ex)
        assert(solverContext.sat())
        /*
        // the old implementation with failure predicates
        rewriter.push()
        val failPreds = nextState.arena.findCellsByType(FailPredT())
        val failureOccurs = tla.or(failPreds.map(_.toNameEx): _*)
        solverContext.assertGroundExpr(failureOccurs)
        assert(solverContext.sat()) // failure should be possible
        */

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-FILTER[1-2]: 3 \in {x \in {2, 3} : x % 2 = 0} ~~> $B$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(2)), ValEx(TlaInt(3)))
    val xMod2 = OperEx(TlaArithOper.mod, NameEx("x"), ValEx(TlaInt(2)))
    val filter = OperEx(TlaOper.eq, xMod2, ValEx(TlaInt(0)))
    val filteredSet = OperEx(TlaSetOper.filter, NameEx("x"), set, filter)
    val inFilteredSet = OperEx(TlaSetOper.in, ValEx(TlaInt(3)), filteredSet)

    val state = new SymbState(inFilteredSet, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, membershipEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-MAP[1-2]: {x / 3: x \in {1,2,3,4}} ~~> $C$k""") {
    val set = tla.enumSet(1 to 4 map tla.int :_*)
    val mapping = tla.div(tla.name("x"), tla.int(3))
    val mappedSet = tla.map(mapping, tla.name("x"), set)

    val state = new SymbState(mappedSet, CellTheory(), arena, new Binding)
    val nextState = create().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
      // membership tests are in the tests below

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-MAP[1-2]: 0 \in {x / 3: x \in {1,2,3,4}} ~~> $B$k""") {
    val set = tla.enumSet(1 to 4 map tla.int :_*)
    val mapping = tla.div(tla.name("x"), tla.int(3))
    val mappedSet = tla.map(mapping, tla.name("x"), set)
    val inMappedSet = tla.in(tla.int(0), mappedSet)

    val state = new SymbState(inMappedSet, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, membershipEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-MAP[1-2]: 2 \in {x / 3: x \in {1,2,3,4}} ~~> $B$k""") {
    val set = tla.enumSet(1 to 4 map tla.int :_*)
    val mapping = tla.div(tla.name("x"), tla.int(3))
    val mappedSet = tla.map(mapping, tla.name("x"), set)
    val inMappedSet = tla.in(tla.int(2), mappedSet)

    val state = new SymbState(inMappedSet, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, membershipEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-MAP[1-2]: <<2, true>> \in {<<x, y>>: x \in {1,2,3}, y \in {FALSE, TRUE}} ~~> $B$k""") {
    val set123 = tla.enumSet(1 to 3 map tla.int :_*)
    val setBool = tla.enumSet(tla.bool(false), tla.bool(true))
    val mapping = tla.tuple(tla.name("x"), tla.name("y"))
    val mappedSet = tla.map(mapping, tla.name("x"), set123, tla.name("y"), setBool)
    val inMappedSet = tla.in(tla.tuple(tla.int(2), tla.bool(true)), mappedSet)

    val state = new SymbState(inMappedSet, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, membershipEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // FIXME: fix asap, this is soundness issue
  ignore("""SE-SET-MAP[1-2]: <<TRUE>> \in {<<y>>: x \in {1,2} \ {2}, y \in {FALSE, TRUE}} ~~> $B$k""") {
    // this expression may be problematic as it might conflict with cached expressions
    val set12 = tla.enumSet(1 to 2 map tla.int :_*)
    val set12minus2 = tla.setminus(set12, tla.enumSet(tla.int(2)))
    val setBool = tla.enumSet(tla.bool(false), tla.bool(true))
    val mapping = tla.tuple(tla.name("y"))
    val mappedSet = tla.map(mapping, tla.name("x"), set12minus2, tla.name("y"), setBool)
    val inMappedSet = tla.in(tla.tuple(tla.bool(true)), mappedSet)

    val state = new SymbState(inMappedSet, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, membershipEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-CUP[1-2]: {1, 3} \cup {3, 4} = {1, 3, 4}""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(3)))
    val right = mkSet(ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val expected = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val cupSet = OperEx(TlaSetOper.cup, left, right)
    val eqExpected = OperEx(TlaOper.eq, cupSet, expected)

    val state = new SymbState(eqExpected, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(solverContext.sat())
        // check equality
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-CAP[1-2]: {1, 3} \cap {3, 4} = {3}""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(3)))
    val right = mkSet(ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val expected = mkSet(ValEx(TlaInt(3)))
    val capSet = OperEx(TlaSetOper.cap, left, right)
    val eqExpected = OperEx(TlaOper.eq, capSet, expected)

    val state = new SymbState(eqExpected, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(solverContext.sat())
        // check equality
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-DIFF[1-2]: {1, 3, 5} \cap {1, 4} = {3, 5}""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(3)), ValEx(TlaInt(5)))
    val right = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(4)))
    val expected = mkSet(ValEx(TlaInt(3)), ValEx(TlaInt(5)))
    val minusSet = OperEx(TlaSetOper.setminus, left, right)
    val eqExpected = OperEx(TlaOper.eq, minusSet, expected)

    val state = new SymbState(eqExpected, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(solverContext.sat())
        // check equality
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-CUP: regression""") {
    // 2019-01-18, Igor: this bug originally appeared in TwoPhase.tla, the MWE can be found in Bug20190118.tla
    // S = {1} \ {1}
    val set1 = tla.setminus(tla.enumSet(tla.int(1)), tla.enumSet(tla.int(1)))
    // T = {3} \ 3
    val set2 = tla.setminus(tla.enumSet(tla.int(3)), tla.enumSet(tla.int(3)))
    // R = S \cup T = {}
    val set3 = tla.cup(set1, set2) // the buggy implementation will try in(1, T) and this may return true!
    val trans = tla.in(tla.int(1), set3)
    val state = new SymbState(trans, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat()) // in the buggy implementation, 1 \ in R

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSETEQ[1-3]: {1, 2} \subseteq {1, 2, 3} ~~> $B$... (true)""") {
    val left = tla.enumSet(tla.int(1), tla.int(2))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subseteq(left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSETEQ[1-3]: {1, 2, 3} \subseteq {1, 2, 3} ~~> $B$... (true)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subseteq(right, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSETEQ[1-3]: {} \subseteq {1, 2, 3} ~~> $B$... (true)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    // an empty set requires a type annotation
    val ex = tla.subseteq(emptySetWithType(IntT()), right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSETEQ[1-3]: {1, 4} \subseteq {1, 2, 3} ~~> $B$... (false)""") {
    val left = tla.enumSet(tla.int(1), tla.int(4))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subseteq(left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(rewriter, nextState)
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUPSETEQ[1-3]: {1, 2, 3} \supseteq {1, 2} ~~> $B$... (true)""") {
    val left = tla.enumSet(tla.int(1), tla.int(2))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.supseteq(right, left)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUPSETEQ[1-3]: {1, 2, 3} \supseteq {1, 2, 3} ~~> $B$... (true)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.supseteq(right, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUPSETEQ[1-3]: {1, 2, 3} \supseteq {} ~~> $B$... (true)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    // an empty set requires a type annotation
    val ex = tla.supseteq(right, emptySetWithType(IntT()))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUPSETEQ[1-3]: {1, 2, 3} \supseteq {1, 4} ~~> $B$... (false)""") {
    val left = tla.enumSet(tla.int(1), tla.int(4))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.supseteq(right, left)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(rewriter, nextState)
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET[1-3]: {1, 2} \subset {1, 2, 3} ~~> $B$... (true)""") {
    val left = tla.enumSet(tla.int(1), tla.int(2))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subset(left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET[1-3]: {1, 2, 3} \subset {1, 2, 3} ~~> $B$... (false)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subset(right, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(rewriter, nextState)
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET[1-3]: {} \subset {1, 2, 3} ~~> $B$... (true)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    // an empty set requires a type annotation
    val ex = tla.subset(emptySetWithType(IntT()), right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET[1-3]: {1, 4} \subset {1, 2, 3} ~~> $B$... (false)""") {
    val left = tla.enumSet(tla.int(1), tla.int(4))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subset(left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(rewriter, nextState)
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""type inference error: {1, 3} \subset {{1}, {2}, {3}}""") {
    // this test worked in the past but now it reports a type inference error
    val left = tla.enumSet(tla.int(1), tla.int(3))
    val right = tla.enumSet(tla.enumSet(tla.int(1)), tla.enumSet(tla.int(2)), tla.enumSet(tla.int(3)))
    val ex = tla.subset(left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    assertThrows[TypeInferenceError] {
      rewriter.rewriteUntilDone(state)
    }
  }

  test("""SE-SUPSET[1-3]:  {1, 2, 3} \supset {1, 2} ~~> $B$... (true)""") {
    val left = tla.enumSet(tla.int(1), tla.int(2))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.supset(right, left)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUPSET[1-3]: {1, 2, 3} \supset {1, 2, 3} ~~> $B$... (false)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.supset(right, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(rewriter, nextState)
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUPSET[1-3]: {1, 2, 3} \supset {} ~~> $B$... (true)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    // an empty set requires a type annotation
    val ex = tla.supset(right, emptySetWithType(IntT()))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET[1-3]: {1, 2, 3} \subset {1, 4} ~~> $B$... (false)""") {
    val left = tla.enumSet(tla.int(1), tla.int(4))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subset(right, left)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(rewriter, nextState)
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-UNION: UNION {{1, 2}, {2,3}} = {1, 2, 3}""") {
    val setOf12 = tla.enumSet(tla.int(1), tla.int(2))
    val setOf23 = tla.enumSet(tla.int(3), tla.int(2))
    val setOf123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    // This may seem weird, but since we don't know the type of {},
    // it should be equal to the empty set of ints.
    val eq = OperEx(TlaOper.eq, tla.union(tla.enumSet(setOf12, setOf23)), setOf123)
    val rewriter = create()
    val state = new SymbState(eq, BoolTheory(), arena, new Binding)
    assertTlaExAndRestore(rewriter, state)
  }

}
