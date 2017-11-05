package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{BoolT, IntT, UnknownT}
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaOper, TlaSetOper}
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
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, nextState.ex, nextState.arena.cellFalse().toNameEx))
        solverContext.assertGroundExpr(NameEx(pred))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected coercion result")
    }
  }

  test("SE-BOX-BOOL1: $B$_0 ~~> $C$_0") {
    val state = new SymbState(NameEx(solverContext.falseConst),
      BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().coerce(state, CellTheory())
    nextState.ex match {
      case NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(CellTheory() == nextState.theory)
        assert(arena.cellFalse().toString == name)

      case _ =>
        fail("Unexpected coercion result")
    }
  }

  test("SE-BOX-BOOL1: $B$_1 ~~> $C$_1") {
    val state = new SymbState(NameEx(solverContext.trueConst),
      BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().coerce(state, CellTheory())
    nextState.ex match {
      case NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(CellTheory() == nextState.theory)
        assert(arena.cellTrue().toString == name)

      case _ =>
        fail("Unexpected coercion result")
    }
  }

  test("SE-UNBOX-BOOL1: $C$_j ~~> $B$_i") {
    arena = arena.appendCell(BoolT())
    val newCell = arena.topCell
    val state = new SymbState(newCell.toNameEx, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().coerce(state, BoolTheory())
    nextState.ex match {
      case NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == nextState.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, newCell.toNameEx, nextState.arena.cellFalse().toNameEx))
        solverContext.assertGroundExpr(NameEx(name))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected coercion result")
    }
  }

  test("SE-UNBOX-BOOL1: $C$_0 ~~> $B$_0") {
    val state = new SymbState(arena.cellFalse().toNameEx,
      CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().coerce(state, BoolTheory())
    nextState.ex match {
      case NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == nextState.theory)
        assert(solverContext.falseConst == name)

      case _ =>
        fail("Unexpected coercion result")
    }
  }

  test("SE-UNBOX-BOOL1: $C$_1 ~~> $B$_1") {
    val state = new SymbState(arena.cellTrue().toNameEx,
      CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().coerce(state, BoolTheory())
    nextState.ex match {
      case NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == nextState.theory)
        assert(solverContext.trueConst == name)

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
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, nextState.ex, ValEx(TlaInt(42))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(intConst), ValEx(TlaInt(42))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(intConst), ValEx(TlaInt(41))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected coercion result")
    }
  }

  test("SE-UNBOX-INT1: $C$_i ~~> $Z$_j") {
    arena = arena.appendCell(IntT())
    val newCell = arena.topCell
    val state = new SymbState(newCell.toNameEx, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().coerce(state, IntTheory())
    nextState.ex match {
      case NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == nextState.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, nextState.ex, ValEx(TlaInt(42))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, newCell.toNameEx, ValEx(TlaInt(42))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, newCell.toNameEx, ValEx(TlaInt(41))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected coercion result")
    }
  }

  test("SE-SUBST1: x[cell/x] ~~> cell") {
    val newArena = arena.appendCell(UnknownT())
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

  test("SE-BOOL-FALSE [Cell]: FALSE ~~> $C$0") {
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

  test("SE-BOOL-FALSE [Bool]: FALSE ~~> $B$0") {
    val ex = ValEx(TlaFalse)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx("$B$0") == nextState.ex)
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

  test("SE-BOOL-TRUE [Cell]: TRUE ~~> $C$1") {
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

  test("SE-BOOL-TRUE [Bool]: TRUE ~~> $B$1") {
    val ex = ValEx(TlaTrue)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$B$1")
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
        val expected =
          OperEx(TlaBoolOper.equiv,
            OperEx(TlaBoolOper.not, NameEx("x")), NameEx("y"))
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

  test("""SE-BOOL-NEG9: ~c_i ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val cell = arena.topCell

    val ex = OperEx(TlaBoolOper.not, cell.toNameEx)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(BoolTheory().hasConst(name))
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, cell.toNameEx, arena.cellFalse().toNameEx))
            solverContext.assertGroundExpr(nextState.ex)
            solverContext.push()
            assert(solverContext.sat())
            solverContext.pop()
            solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, nextState.ex))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-AND1: FALSE /\ TRUE ~~> $B$0""") {
    val ex = OperEx(TlaBoolOper.and, ValEx(TlaFalse), ValEx(TlaTrue))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx(nextState.solverCtx.falseConst) == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-AND4: c_1 /\ c_2 ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val c1 = arena.topCell
    arena = arena.appendCell(BoolT())
    val c2 = arena.topCell

    val ex = OperEx(TlaBoolOper.and, c1.toNameEx, c2.toNameEx)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(BoolTheory().hasConst(name))
            assert(solverContext.sat())
            solverContext.assertGroundExpr(nextState.ex)
            solverContext.push()
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, c1.toNameEx, arena.cellFalse().toNameEx))
            assert(!solverContext.sat())
            solverContext.pop()
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, c1.toNameEx, arena.cellTrue().toNameEx))
            assert(solverContext.sat())
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, c2.toNameEx, arena.cellTrue().toNameEx))
            assert(solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-OR4: empty \/ ~~> $B$0""") {
    val ex = OperEx(TlaBoolOper.or)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx(solverContext.falseConst) == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-AND4: empty /\ ~~> $B$1""") {
    val ex = OperEx(TlaBoolOper.and)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx(solverContext.trueConst) == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-OR1: FALSE \/ TRUE ~~> $B$1""") {
    val ex = OperEx(TlaBoolOper.or, ValEx(TlaFalse), ValEx(TlaTrue))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx(solverContext.trueConst) == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-OR5: c_1 \/ c_2 ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val left = arena.topCell
    arena = arena.appendCell(BoolT())
    val right = arena.topCell

    val ex = OperEx(TlaBoolOper.or, left.toNameEx, right.toNameEx)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(BoolTheory().hasConst(name))
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, left.toNameEx, arena.cellFalse().toNameEx))
            solverContext.assertGroundExpr(nextState.ex)
            solverContext.push()
            assert(solverContext.sat())
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, right.toNameEx, arena.cellFalse().toNameEx))
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
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
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
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    assert(NameEx(solverContext.falseConst) == nextState.ex)
  }

  test("""SE-SET-IN1: 3 \in {1, 3, 5} ~~> $B$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ex = OperEx(TlaSetOper.in,
      ValEx(TlaInt(3)),
      mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(3)), ValEx(TlaInt(5))))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN1: {3} \in {1, {3}, {5}} ~~> $B$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ex = OperEx(TlaSetOper.in,
      mkSet(ValEx(TlaInt(3))),
      mkSet(ValEx(TlaInt(1)), mkSet(ValEx(TlaInt(3))), mkSet(ValEx(TlaInt(5)))))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        solverContext.pop()
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
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-IN1: 3 \in {1, {3}, {5}} ~~> $B$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ex = OperEx(TlaSetOper.in,
      ValEx(TlaInt(3)),
      mkSet(ValEx(TlaInt(1)), mkSet(ValEx(TlaInt(3))), mkSet(ValEx(TlaInt(5)))))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-NOTIN1: {} \notin {} ~~> $B$1""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ex = OperEx(TlaSetOper.notin, mkSet(), mkSet())
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    assert(NameEx(solverContext.trueConst) == nextState.ex)
  }

  test("""SE-SET-IN2: \FALSE \in {\FALSE, \TRUE} ~~> b_new""") {
    val ex =
      OperEx(TlaSetOper.in,
        ValEx(TlaFalse),
        OperEx(TlaSetOper.enumSet, ValEx(TlaFalse), ValEx(TlaTrue)))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx@NameEx(name) =>
            assert(BoolTheory().hasConst(name))
            solverContext.push()
            solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
            assert(!solverContext.sat())
            solverContext.pop()
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
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteUntilDone(state).ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())
        solverContext.pop()
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
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx@NameEx(name) =>
            assert(BoolTheory().hasConst(name))
            solverContext.push()
            // cell = \TRUE
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, cell.toNameEx))
            // and membership holds true
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())
            solverContext.pop()
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

  test("""SE-SET-NOTIN1: c_i: Bool \notin {\TRUE, \TRUE} ~~> c_pred""") {
    arena = arena.appendCell(BoolT())
    val cell = arena.topCell
    val ex =
      OperEx(TlaSetOper.notin,
        cell.toNameEx,
        OperEx(TlaSetOper.enumSet, ValEx(TlaTrue), ValEx(TlaTrue)))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteUntilDone(state).ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        // cell = \TRUE
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, arena.cellTrue().toNameEx, cell.toNameEx))
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        solverContext.pop()
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
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        solverContext.pop()
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
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        solverContext.pop()
        // another query
        // and membership does not hold
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-EQ1: {{}, {{}}} = {{}, {{{}}} ~~> $B$... (false)""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = mkSet(mkSet(), mkSet(mkSet()))
    val right = mkSet(mkSet(), mkSet(mkSet(mkSet())))
    val ex = OperEx(TlaOper.eq, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
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
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SET-NE1: {{}, {{}}} != {{}, {{}} ~~> $B$... (false)""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = mkSet(mkSet(), mkSet(mkSet()))
    val right = mkSet(mkSet(), mkSet(mkSet()))
    val ex = OperEx(TlaOper.ne, left, right)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-CELL-EQ1: $C$_i: Int = $C$_j: Int ~~> valInt(...) = valInt(...)") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val state = new SymbState(OperEx(TlaOper.eq, leftCell.toNameEx, rightCell.toNameEx),
      BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, leftCell.toNameEx, ValEx(TlaInt(22))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(22))))
        solverContext.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(1981))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())


      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-EQ1: $Z$i = $Z$j ~~> $B$k") {
    val leftInt = solverContext.introIntConst()
    val rightInt = solverContext.introIntConst()
    val state = new SymbState(OperEx(TlaOper.eq, NameEx(leftInt), NameEx(rightInt)),
      BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(22))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(22))))
        solverContext.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(1981))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NE1: $B$1 != $B$2 ~~> $B$3""") {
    arena = arena.appendCell(BoolT())
    val left = arena.topCell
    arena = arena.appendCell(BoolT())
    val right = arena.topCell

    val ex = OperEx(TlaOper.ne, left.toNameEx, right.toNameEx)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.assertGroundExpr(predEx)
        solverContext.push()
        // both false
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, left.toNameEx, arena.cellFalse().toNameEx))
        assert(solverContext.sat())
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, right.toNameEx, arena.cellFalse().toNameEx))
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, right.toNameEx, arena.cellTrue().toNameEx))
        assert(solverContext.sat())
        solverContext.pop()
        // both true
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, left.toNameEx, arena.cellTrue().toNameEx))
        assert(solverContext.sat())
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, right.toNameEx, arena.cellTrue().toNameEx))
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, right.toNameEx, arena.cellFalse().toNameEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-CELL-CMP1: $C$_i: Int < $C$_j: Int ~~> valInt(...) < valInt(...)") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val state = new SymbState(OperEx(TlaArithOper.lt, leftCell.toNameEx, rightCell.toNameEx),
      BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, leftCell.toNameEx, ValEx(TlaInt(4))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(22))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(4))))
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(3))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-CELL-CMP1: $C$_i: Int <= $C$_j: Int ~~> valInt(...) <= valInt(...)") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val state = new SymbState(OperEx(TlaArithOper.le, leftCell.toNameEx, rightCell.toNameEx),
      BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, leftCell.toNameEx, ValEx(TlaInt(4))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(22))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(4))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(3))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-CELL-CMP1: $C$_i: Int > $C$_j: Int ~~> valInt(...) > valInt(...)") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val state = new SymbState(OperEx(TlaArithOper.gt, leftCell.toNameEx, rightCell.toNameEx),
      BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, leftCell.toNameEx, ValEx(TlaInt(4))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(22))))
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(4))))
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(3))))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-CMP1 (composite expressions): 1 + 5 > 6 - 3 ~~> $B$_k") {
    val left = OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), ValEx(TlaInt(5)))
    val right = OperEx(TlaArithOper.minus, ValEx(TlaInt(6)), ValEx(TlaInt(3)))
    val state = new SymbState(OperEx(TlaArithOper.gt, left, right),
      BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.push()
        solverContext.assertGroundExpr(cmpEx)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, cmpEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-CELL-CMP1: $C$_i: Int >= $C$_j: Int ~~> valInt(...) >= valInt(...)") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val state = new SymbState(OperEx(TlaArithOper.ge, leftCell.toNameEx, rightCell.toNameEx),
      BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, leftCell.toNameEx, ValEx(TlaInt(4))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(22))))
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(4))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(3))))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-CMP1: $Z$i != $Z$j ~~> $B$k") {
    val leftInt = solverContext.introIntConst()
    val rightInt = solverContext.introIntConst()
    val state = new SymbState(OperEx(TlaOper.ne, NameEx(leftInt), NameEx(rightInt)),
      BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(22))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(22))))
        solverContext.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(1981))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-ARITH1[+]: $Z$i + $Z$j ~~> $Z$k") {
    val leftInt = solverContext.introIntConst()
    val rightInt = solverContext.introIntConst()
    val expr = OperEx(TlaArithOper.plus, NameEx(leftInt), NameEx(rightInt))
    val state = new SymbState(expr, IntTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(1981))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(36))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(2017))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(2016))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-ARITH1[-]: $Z$i - $Z$j ~~> $Z$k") {
    val leftInt = solverContext.introIntConst()
    val rightInt = solverContext.introIntConst()
    val expr = OperEx(TlaArithOper.minus, NameEx(leftInt), NameEx(rightInt))
    val state = new SymbState(expr, IntTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(2017))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(36))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(1981))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(1980))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-ARITH1[*]: $Z$i * $Z$j ~~> $Z$k") {
    val leftInt = solverContext.introIntConst()
    val rightInt = solverContext.introIntConst()
    val expr = OperEx(TlaArithOper.mult, NameEx(leftInt), NameEx(rightInt))
    val state = new SymbState(expr, IntTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(7))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(4))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(28))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(30))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-ARITH1[/]: $Z$i / $Z$j ~~> $Z$k") {
    val leftInt = solverContext.introIntConst()
    val rightInt = solverContext.introIntConst()
    val expr = OperEx(TlaArithOper.div, NameEx(leftInt), NameEx(rightInt))
    val state = new SymbState(expr, IntTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(30))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(4))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(7))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(8))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-ARITH1[%]: $Z$i % $Z$j ~~> $Z$k") {
    val leftInt = solverContext.introIntConst()
    val rightInt = solverContext.introIntConst()
    val expr = OperEx(TlaArithOper.mod, NameEx(leftInt), NameEx(rightInt))
    val state = new SymbState(expr, IntTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(30))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(7))))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(2))))
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(1))))
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
    val state = new SymbState(ex, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case newSet @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        solverContext.push()
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

    val state = new SymbState(inFilteredSet, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        solverContext.pop()
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

    val state = new SymbState(inFilteredSet, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        solverContext.pop()
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

    val state = new SymbState(mappedSet, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
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

    val state = new SymbState(inMappedSet, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        solverContext.pop()
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

    val state = new SymbState(inMappedSet, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        solverContext.pop()
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
    val unionSet = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val cupSet = OperEx(TlaSetOper.cup, left, right)
    val cupSetEqUnion = OperEx(TlaOper.eq, cupSet, unionSet)

    val state = new SymbState(cupSetEqUnion, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(solverContext.sat())
        // check equality
        solverContext.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        solverContext.pop()
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
    val unionSet = mkSet(ValEx(TlaInt(3)))
    val capSet = OperEx(TlaSetOper.cap, left, right)
    val capSetEqUnion = OperEx(TlaOper.eq, capSet, unionSet)

    val state = new SymbState(capSetEqUnion, BoolTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(solverContext.sat())
        // check equality
        solverContext.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}