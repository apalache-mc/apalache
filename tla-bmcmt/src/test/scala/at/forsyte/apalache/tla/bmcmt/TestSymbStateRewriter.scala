package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{BoolType, IntType, UnknownType}
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.predef.TlaBoolSet
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaInt, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfter, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriter extends FunSuite with BeforeAndAfter {
  private var solverContext: SolverContext = new Z3SolverContext()
  private var arena: Arena = Arena.create(solverContext)

  before {
    solverContext = new Z3SolverContext()
    arena = Arena.create(solverContext)
  }

  after {
    solverContext.dispose()
  }

  test("SE-BOX-BOOL1: $B$_i ~~> $C$_j") {
    val pred = solverContext.introBoolConst()
    val state = new SymbState(NameEx(pred), BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().coerce(state, CellTheory())
    nextState.ex match {
      case NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(CellTheory() == nextState.theory)
        assert(solverContext.sat())
        solverContext.assertCellExpr(OperEx(TlaOper.eq, nextState.ex, nextState.arena.cellFalse().toNameEx))
        solverContext.assertCellExpr(NameEx(pred))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected coercion result")
    }
  }

  test("SE-UNBOX-BOOL1: $C$_j ~~> $B$_i") {
    arena = arena.appendCell(BoolType())
    val newCell = arena.topCell
    val state = new SymbState(newCell.toNameEx, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().coerce(state, BoolTheory())
    nextState.ex match {
      case NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == nextState.theory)
        assert(solverContext.sat())
        solverContext.assertCellExpr(OperEx(TlaOper.eq, newCell.toNameEx, nextState.arena.cellFalse().toNameEx))
        solverContext.assertCellExpr(NameEx(name))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected coercion result")
    }
  }

  test("SE-BOX-INT1: $Z$_i ~~> $C$_j") {
    val intConst = solverContext.introIntConst()
    val state = new SymbState(NameEx(intConst), IntTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().coerce(state, CellTheory())
    nextState.ex match {
      case NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(CellTheory() == nextState.theory)
        assert(solverContext.sat())
        solverContext.assertCellExpr(OperEx(TlaOper.eq, nextState.ex, ValEx(TlaInt(42))))
        solverContext.push()
        solverContext.assertCellExpr(OperEx(TlaOper.eq, NameEx(intConst), ValEx(TlaInt(42))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertCellExpr(OperEx(TlaOper.eq, NameEx(intConst), ValEx(TlaInt(41))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected coercion result")
    }
  }

  test("SE-UNBOX-INT1: $C$_i ~~> $Z$_j") {
    arena = arena.appendCell(IntType())
    val newCell = arena.topCell
    val state = new SymbState(newCell.toNameEx, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().coerce(state, IntTheory())
    nextState.ex match {
      case NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == nextState.theory)
        assert(solverContext.sat())
        solverContext.assertCellExpr(OperEx(TlaOper.eq, nextState.ex, ValEx(TlaInt(42))))
        solverContext.push()
        solverContext.assertCellExpr(OperEx(TlaOper.eq, newCell.toNameEx, ValEx(TlaInt(42))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertCellExpr(OperEx(TlaOper.eq, newCell.toNameEx, ValEx(TlaInt(41))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected coercion result")
    }
  }

  test("SE-SUBST1: x[cell/x] ~~> cell") {
    val newArena = arena.appendCell(UnknownType())
    val cell = newArena.topCell
    val binding = new Binding() + ("x" -> cell)
    val state = new SymbState(NameEx("x"), CellTheory(), arena, binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Done(nextState) =>
        val expected = NameEx("$C$%d".format(cell.id))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOX-FALSE: FALSE ~~> c_FALSE") {
    val ex = ValEx(TlaFalse)
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$0")
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-SET-BOOLEAN: BOOLEAN ~~> c_BOOLEAN") {
    val state = new SymbState(ValEx(TlaBoolSet), CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$2")
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOX-TRUE: TRUE ~~> c_TRUE") {
    val ex = ValEx(TlaTrue)
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$1")
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG1: ~(x \/ y) ~~> ~x /\ ~y""") {
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.or, NameEx("x"), NameEx("y")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.and,
          OperEx(TlaBoolOper.not, NameEx("x")),
          OperEx(TlaBoolOper.not, NameEx("y")))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG2: ~(x /\ y) ~~> ~x \/ ~y""") {
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.and, NameEx("x"), NameEx("y")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.or,
          OperEx(TlaBoolOper.not, NameEx("x")),
          OperEx(TlaBoolOper.not, NameEx("y")))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-NEG3: ~(x => y) ~~> x /\\ ~y") {
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.implies, NameEx("x"), NameEx("y")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.and,
          NameEx("x"),
          OperEx(TlaBoolOper.not, NameEx("y")))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-NEG4: ~(x <=> y) ~~> ~x <=> y") {
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.equiv, NameEx("x"), NameEx("y")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.equiv,
          OperEx(TlaBoolOper.not, NameEx("x")),
          NameEx("y"))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-NEG5: ~~x ~~> x") {
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.not, NameEx("x")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx("x") == nextState.ex)
        assert(state.arena == nextState.arena)
        assert(state.binding == nextState.binding)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG6: ~\E x \in S: p ~~> \A x \in S: ~p""") {
    val ex = OperEx(TlaBoolOper.not,
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("S"), NameEx("p")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.forall, NameEx("x"), NameEx("S"),
          OperEx(TlaBoolOper.not, NameEx("p")))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)
        assert(state.binding == nextState.binding)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG7: ~\A x \in S: p ~~> \E x \in S: ~p""") {
    val ex = OperEx(TlaBoolOper.not,
      OperEx(TlaBoolOper.forall, NameEx("x"), NameEx("S"), NameEx("p")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("S"),
          OperEx(TlaBoolOper.not, NameEx("p")))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)
        assert(state.binding == nextState.binding)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG9: ~c_i ~~> c_new""") {
    arena = arena.appendCell(BoolType())
    val cell = arena.topCell

    val ex = OperEx(TlaBoolOper.not, cell.toNameEx)
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(CellTheory().hasConst(name))
            solverContext.assertCellExpr(OperEx(TlaOper.eq, cell.toNameEx, arena.cellFalse().toNameEx))
            solverContext.assertCellExpr(OperEx(TlaOper.eq, nextState.ex, arena.cellTrue().toNameEx))
            solverContext.push()
            assert(solverContext.sat())
            solverContext.pop()
            solverContext.assertCellExpr(OperEx(TlaOper.eq, nextState.ex, arena.cellFalse().toNameEx))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-AND1: FALSE /\ TRUE ~~> c_FALSE""") {
    val ex = OperEx(TlaBoolOper.and, ValEx(TlaFalse), ValEx(TlaTrue))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx(nextState.arena.cellFalse().toString) == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-AND4: c_1 /\ c_2 ~~> c_new""") {
    arena = arena.appendCell(BoolType())
    val c1 = arena.topCell
    arena = arena.appendCell(BoolType())
    val c2 = arena.topCell

    val ex = OperEx(TlaBoolOper.and, c1.toNameEx, c2.toNameEx)
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(CellTheory().hasConst(name))
            solverContext.push()
            assert(solverContext.sat())
            solverContext.assertCellExpr(OperEx(TlaOper.eq, c1.toNameEx, arena.cellFalse().toNameEx))
            solverContext.assertCellExpr(OperEx(TlaOper.eq, nextState.ex, arena.cellTrue().toNameEx))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-OR1: FALSE \/ TRUE ~~> c_TRUE""") {
    val ex = OperEx(TlaBoolOper.or, ValEx(TlaFalse), ValEx(TlaTrue))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx(nextState.arena.cellTrue().toString) == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-OR4: c_1 \/ c_2 ~~> c_new""") {
    arena = arena.appendCell(BoolType())
    val c1 = arena.topCell
    arena = arena.appendCell(BoolType())
    val c2 = arena.topCell

    val ex = OperEx(TlaBoolOper.or, c1.toNameEx, c2.toNameEx)
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(CellTheory().hasConst(name))
            solverContext.assertCellExpr(OperEx(TlaOper.eq, c1.toNameEx, arena.cellFalse().toNameEx))
            solverContext.assertCellExpr(OperEx(TlaOper.eq, nextState.ex, arena.cellTrue().toNameEx))
            solverContext.push()
            assert(solverContext.sat())
            solverContext.assertCellExpr(OperEx(TlaOper.eq, c2.toNameEx, arena.cellFalse().toNameEx))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-CTOR[1-2]: {x, y, z} ~~> c_set""") {
    val ex = OperEx(TlaSetOper.enumSet, NameEx("x"), NameEx("y"), NameEx("z"))
    val binding = new Binding + ("x" -> arena.cellFalse()) +
      ("y" -> arena.cellTrue()) + ("z" -> arena.cellFalse())
    val state = new SymbState(ex, CellTheory(), arena, binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case set@NameEx(name) =>
            assert(CellTheory().hasConst(name))
            solverContext.assertCellExpr(OperEx(TlaSetOper.in, arena.cellFalse().toNameEx, set))
            assert(solverContext.sat())
            solverContext.assertCellExpr(OperEx(TlaBoolOper.not,
              OperEx(TlaSetOper.in, arena.cellTrue().toNameEx, set)))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN1: {} \in {} ~~> c_\FALSE""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ex = OperEx(TlaSetOper.in, mkSet(), mkSet())
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    assert(nextState.arena.cellFalse().toNameEx == nextState.ex)
  }

  test("""SE-SET-NOTIN1: {} \notin {} ~~> c_\TRUE""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ex = OperEx(TlaSetOper.notin, mkSet(), mkSet())
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    assert(nextState.arena.cellTrue().toNameEx == nextState.ex)
  }

  test("""SE-SET-IN2: \FALSE \in {\FALSE, \TRUE} ~~> c_pred""") {
    val ex =
      OperEx(TlaSetOper.in,
        ValEx(TlaFalse),
        OperEx(TlaSetOper.enumSet, ValEx(TlaFalse), ValEx(TlaTrue)))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx@NameEx(name) =>
            assert(CellTheory().hasConst(name))
            solverContext.push()
            solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellFalse().toNameEx, predEx))
            assert(!solverContext.sat())
            solverContext.pop()
            solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, predEx))
            assert(solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-NOTIN1: \FALSE \notin {\FALSE, \TRUE} ~~> c_pred""") {
    val ex =
      OperEx(TlaSetOper.notin,
        ValEx(TlaFalse),
        OperEx(TlaSetOper.enumSet, ValEx(TlaFalse), ValEx(TlaTrue)))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteUntilDone(state).ex match {
      case predEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        solverContext.push()
        solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellFalse().toNameEx, predEx))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, predEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN3: c_i: Bool \in {\TRUE, \TRUE} ~~> c_pred""") {
    arena = arena.appendCell(BoolType())
    val cell = arena.topCell
    val ex =
      OperEx(TlaSetOper.in,
        cell.toNameEx,
        OperEx(TlaSetOper.enumSet, ValEx(TlaTrue), ValEx(TlaTrue)))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx@NameEx(name) =>
            assert(CellTheory().hasConst(name))
            solverContext.push()
            // cell = \TRUE
            solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, cell.toNameEx))
            // and membership holds true
            solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, predEx))
            assert(solverContext.sat())
            solverContext.pop()
            // another query
            // cell = \FALSE
            solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellFalse().toNameEx, cell.toNameEx))
            // and membership holds true
            solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, predEx))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-NOTIN1: c_i: Bool \notin {\TRUE, \TRUE} ~~> c_pred""") {
    arena = arena.appendCell(BoolType())
    val cell = arena.topCell
    val ex =
      OperEx(TlaSetOper.notin,
        cell.toNameEx,
        OperEx(TlaSetOper.enumSet, ValEx(TlaTrue), ValEx(TlaTrue)))
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteUntilDone(state).ex match {
      case predEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        solverContext.push()
        // cell = \TRUE
        solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, cell.toNameEx))
        // and membership holds true
        solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, predEx))
        assert(!solverContext.sat())
        solverContext.pop()
        // another query
        // cell = \FALSE
        solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellFalse().toNameEx, cell.toNameEx))
        // and membership holds true
        solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN3: {{}, {{}, {}}} \in {{}, {{}, {{}, {}}}} ~~> c_pred""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = mkSet(mkSet(), mkSet(mkSet(), mkSet()))
    val right = mkSet(mkSet(), mkSet(mkSet(), mkSet(mkSet(), mkSet())))
    val ex = OperEx(TlaSetOper.in, left, right)
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        solverContext.push()
        // and membership holds true
        solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, predEx))
        assert(solverContext.sat())
        solverContext.pop()
        // another query
        // and membership does not hold
        solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellFalse().toNameEx, predEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN3: {{}, {{{}}}} \in {{}, {{}, {{}}} ~~> c_pred""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = mkSet(mkSet(), mkSet(mkSet(mkSet())))
    val right = mkSet(mkSet(), mkSet(mkSet(), mkSet(mkSet())))
    val ex = OperEx(TlaSetOper.in, left, right)
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        solverContext.push()
        // and membership holds true
        solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, predEx))
        assert(!solverContext.sat())
        solverContext.pop()
        // another query
        // and membership does not hold
        solverContext.assertCellExpr(OperEx(TlaOper.eq, arena.cellFalse().toNameEx, predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
