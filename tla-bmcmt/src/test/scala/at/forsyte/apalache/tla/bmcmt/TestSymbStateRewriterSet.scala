package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{BoolT, IntT}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaInt, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterSet extends RewriterBase {
  test("""SE-SET-CTOR[1-2]: {x, y, z} ~~> c_set""") {
    val ex = OperEx(TlaSetOper.enumSet, NameEx("x"), NameEx("y"), NameEx("z"))
    val binding = new Binding + ("x" -> arena.cellFalse()) +
      ("y" -> arena.cellTrue()) + ("z" -> arena.cellFalse())
    val state = new SymbState(ex, CellTheory(), arena, binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
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
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
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

    val ex = OperEx(TlaSetOper.in, mkSet(), mkSet())
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val nextState = new SymbStateRewriter(solverContext).rewriteUntilDone(state)
    assert(NameEx(solverContext.falseConst) == nextState.ex)
  }

  test("""SE-SET-IN1: 3 \in {1, 3, 5} ~~> $B$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ex = OperEx(TlaSetOper.in,
      ValEx(TlaInt(3)),
      mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(3)), ValEx(TlaInt(5))))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    val rewriter = new SymbStateRewriter(solverContext)
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
    val rewriter = new SymbStateRewriter(solverContext)
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

  test("""SE-SET-IN1: 3 \in {{1}, {3}, {5}} ~~> $B$k""") {
    val ex = tla.in(tla.int(3),
      tla.enumSet(tla.enumSet(tla.int(1)), tla.enumSet(tla.int(3)), tla.enumSet(tla.int(5))))

    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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

  test("""SE-SET-NOTIN1: {} \notin {} ~~> $B$1""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ex = OperEx(TlaSetOper.notin, mkSet(), mkSet())
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(NameEx(solverContext.trueConst) == nextState.ex)
  }

  test("""SE-SET-IN2: \FALSE \in {\FALSE, \TRUE} ~~> b_new""") {
    val ex =
      OperEx(TlaSetOper.in,
        ValEx(TlaFalse),
        OperEx(TlaSetOper.enumSet, ValEx(TlaFalse), ValEx(TlaTrue)))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    val rewriter = new SymbStateRewriter(solverContext)
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
    val rewriter = new SymbStateRewriter(solverContext)
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
    val rewriter = new SymbStateRewriter(solverContext)
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
    val rewriter = new SymbStateRewriter(solverContext)
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

    val left = mkSet(mkSet(), mkSet(mkSet(), mkSet()))
    val right = mkSet(mkSet(), mkSet(mkSet(), mkSet(mkSet(), mkSet())))
    val ex = OperEx(TlaSetOper.in, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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

    val left = mkSet(mkSet(), mkSet(mkSet(mkSet())))
    val right = mkSet(mkSet(), mkSet(mkSet(), mkSet(mkSet())))
    val ex = OperEx(TlaSetOper.in, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        // another query
        // and membership does not hold
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-EQ1: {{}} = {} ~~> $B$... (false)""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ex = OperEx(TlaOper.eq, tla.enumSet(tla.enumSet()), tla.enumSet())
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = mkSet(mkSet(), mkSet(mkSet()))
    val right = mkSet(mkSet(), mkSet(mkSet(mkSet())))
    val ex = OperEx(TlaOper.eq, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = mkSet(mkSet(), mkSet(mkSet()))
    val right = mkSet(mkSet(), mkSet(mkSet()))
    val ex = OperEx(TlaOper.eq, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    val setOf1 = tla.enumSet(tla.int(1))
    // This may seem weird, but since we don't know the type of {},
    // it should be equal to the empty set of ints.
    val ex = OperEx(TlaOper.eq, tla.enumSet(), tla.setminus(setOf1, setOf1))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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

  test("""SE-SET-EQ1: {1} \ {1} = {FALSE} \ {FALSE} ~~> $B$... (false)""") {
    // This may seem weird too, but since know the types of the both sets,
    // and these types differ from each other, the result should be false
    val setOfOne = tla.enumSet(tla.int(1))
    val setOfFalse = tla.enumSet(tla.bool(false))
    val ex = OperEx(TlaOper.eq,
                    tla.setminus(setOfFalse, setOfFalse),
                    tla.setminus(setOfOne, setOfOne))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        // equal
        solverContext.assertGroundExpr(tla.not(predEx))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-NE1: {{}, {{}}} != {{}, {{}} ~~> $B$... (false)""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = mkSet(mkSet(), mkSet(mkSet()))
    val right = mkSet(mkSet(), mkSet(mkSet()))
    val ex = OperEx(TlaOper.ne, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    val rewriter = new SymbStateRewriter(solverContext)
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

  test("""SE-SET-FILTER[1-2]: 2 \in {x \in {1,2,3,4} : x % 2 = 0} ~~> $B$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val xMod2 = OperEx(TlaArithOper.mod, NameEx("x"), ValEx(TlaInt(2)))
    val filter = OperEx(TlaOper.eq, xMod2, ValEx(TlaInt(0)))
    val filteredSet = OperEx(TlaSetOper.filter, NameEx("x"), set, filter)
    val inFilteredSet = OperEx(TlaSetOper.in, ValEx(TlaInt(2)), filteredSet)

    val state = new SymbState(inFilteredSet, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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

  test("""SE-SET-FILTER[1-2]: 3 \in {x \in {2, 3} : x % 2 = 0} ~~> $B$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(2)), ValEx(TlaInt(3)))
    val xMod2 = OperEx(TlaArithOper.mod, NameEx("x"), ValEx(TlaInt(2)))
    val filter = OperEx(TlaOper.eq, xMod2, ValEx(TlaInt(0)))
    val filteredSet = OperEx(TlaSetOper.filter, NameEx("x"), set, filter)
    val inFilteredSet = OperEx(TlaSetOper.in, ValEx(TlaInt(3)), filteredSet)

    val state = new SymbState(inFilteredSet, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val mapping = OperEx(TlaArithOper.div, NameEx("x"), ValEx(TlaInt(3)))
    val mappedSet = OperEx(TlaSetOper.map, mapping, NameEx("x"), set)

    val state = new SymbState(mappedSet, CellTheory(), arena, new Binding)
    val nextState = new SymbStateRewriter(solverContext).rewriteUntilDone(state)
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
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val mapping = OperEx(TlaArithOper.div, NameEx("x"), ValEx(TlaInt(3)))
    val mappedSet = OperEx(TlaSetOper.map, mapping, NameEx("x"), set)
    val inMappedSet = OperEx(TlaSetOper.in, ValEx(TlaInt(0)), mappedSet)

    val state = new SymbState(inMappedSet, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val mapping = OperEx(TlaArithOper.div, NameEx("x"), ValEx(TlaInt(3)))
    val mappedSet = OperEx(TlaSetOper.map, mapping, NameEx("x"), set)
    val inMappedSet = OperEx(TlaSetOper.in, ValEx(TlaInt(2)), mappedSet)

    val state = new SymbState(inMappedSet, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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

  test("""SE-SET-CUP[1-2]: {1, 3} \cup {3, 4} = {1, 3, 4}""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(3)))
    val right = mkSet(ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val expected = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val cupSet = OperEx(TlaSetOper.cup, left, right)
    val eqExpected = OperEx(TlaOper.eq, cupSet, expected)

    val state = new SymbState(eqExpected, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    val rewriter = new SymbStateRewriter(solverContext)
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
    val rewriter = new SymbStateRewriter(solverContext)
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

  test("""SE-SUBSETEQ[1-3]: {1, 2} \subseteq {1, 2, 3} ~~> $B$... (true)""") {
    val left = tla.enumSet(tla.int(1), tla.int(2))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subseteq(left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
        assertUnsatOrExplain(nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSETEQ[1-3]: {1, 2, 3} \subseteq {1, 2, 3} ~~> $B$... (true)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subseteq(right, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
        assertUnsatOrExplain(nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSETEQ[1-3]: {} \subseteq {1, 2, 3} ~~> $B$... (true)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subseteq(tla.enumSet(), right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
        assertUnsatOrExplain(nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSETEQ[1-3]: {1, 4} \subseteq {1, 2, 3} ~~> $B$... (false)""") {
    val left = tla.enumSet(tla.int(1), tla.int(4))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subseteq(left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(nextState)
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
    val rewriter = new SymbStateRewriter(solverContext)
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
        assertUnsatOrExplain(nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUPSETEQ[1-3]: {1, 2, 3} \supseteq {1, 2, 3} ~~> $B$... (true)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.supseteq(right, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
        assertUnsatOrExplain(nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUPSETEQ[1-3]: {1, 2, 3} \supseteq {} ~~> $B$... (true)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.supseteq(right, tla.enumSet())
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
        assertUnsatOrExplain(nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUPSETEQ[1-3]: {1, 2, 3} \supseteq {1, 4} ~~> $B$... (false)""") {
    val left = tla.enumSet(tla.int(1), tla.int(4))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.supseteq(right, left)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(nextState)
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
    val rewriter = new SymbStateRewriter(solverContext)
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
        assertUnsatOrExplain(nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET[1-3]: {1, 2, 3} \subset {1, 2, 3} ~~> $B$... (false)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subset(right, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(nextState)
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
    val ex = tla.subset(tla.enumSet(), right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
        assertUnsatOrExplain(nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET[1-3]: {1, 4} \subset {1, 2, 3} ~~> $B$... (false)""") {
    val left = tla.enumSet(tla.int(1), tla.int(4))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subset(left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(nextState)
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET[1-3]: {1, 3} \subset {{1}, {2}, {3}} ~~> $B$... (false)""") {
    val left = tla.enumSet(tla.int(1), tla.int(3))
    val right = tla.enumSet(tla.enumSet(tla.int(1)), tla.enumSet(tla.int(2)), tla.enumSet(tla.int(3)))
    val ex = tla.subset(left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(nextState)
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUPSET[1-3]:  {1, 2, 3} \supset {1, 2} ~~> $B$... (true)""") {
    val left = tla.enumSet(tla.int(1), tla.int(2))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.supset(right, left)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
        assertUnsatOrExplain(nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUPSET[1-3]: {1, 2, 3} \supset {1, 2, 3} ~~> $B$... (false)""") {
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.supset(right, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(nextState)
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
    val ex = tla.supset(right, tla.enumSet())
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
        assertUnsatOrExplain(nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET[1-3]: {1, 2, 3} \subset {1, 4} ~~> $B$... (false)""") {
    val left = tla.enumSet(tla.int(1), tla.int(4))
    val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.subset(right, left)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(nextState)
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

}
