package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{BoolType, UnknownType}
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.predef.TlaBoolSet
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, ValEx}
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

  test("SE-SUBST1: x[cell/x] ~~> cell") {
    val newArena = arena.appendCell(UnknownType())
    val cell = newArena.topCell
    val binding = new Binding() + ("x" -> cell)
    val state = new SymbState(NameEx("x"), arena, binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Done(nextState) =>
        val expected = NameEx("$C$%d".format(cell.id))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _@x =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOX-FALSE: FALSE ~~> c_FALSE") {
    val ex = ValEx(TlaFalse)
    val state = new SymbState(ex, arena, new Binding, solverContext)
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
    val state = new SymbState(ValEx(TlaBoolSet), arena, new Binding, solverContext)
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
    val state = new SymbState(ex, arena, new Binding, solverContext)
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
    val state = new SymbState(ex, arena, new Binding, solverContext)
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
    val state = new SymbState(ex, arena, new Binding, solverContext)
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
    val state = new SymbState(ex, arena, new Binding, solverContext)
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
    val state = new SymbState(ex, arena, new Binding, solverContext)
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
    val state = new SymbState(ex, arena, new Binding, solverContext)
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
    val state = new SymbState(ex, arena, new Binding, solverContext)
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
    val state = new SymbState(ex, arena, new Binding, solverContext)
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

  test("""SE-AND1: FALSE /\ TRUE ~~> c_FALSE""") {
    val ex = OperEx(TlaBoolOper.and, ValEx(TlaFalse), ValEx(TlaTrue))
    val state = new SymbState(ex, arena, new Binding, solverContext)
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
    val state = new SymbState(ex, arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(isCellName(name))
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
    val state = new SymbState(ex, arena, new Binding, solverContext)
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
    val state = new SymbState(ex, arena, new Binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(isCellName(name))
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
    val state = new SymbState(ex, arena, binding, solverContext)
    new SymbStateRewriter().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case set @ NameEx(name) =>
            assert(isCellName(name))
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
}
