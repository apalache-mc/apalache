package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter.FastForward
import at.forsyte.apalache.tla.bmcmt.types.UnknownType
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, ValEx}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriter extends FunSuite {
  test("SE-SUBST1: x[cell/x] ~~> cell") {
    val solverCtx = new Z3SolverContext()
    val arena = Arena.create()
    val newArena = arena.appendCell(UnknownType())
    val cell = newArena.topCell
    val binding = new Binding() + ("x" -> cell)
    val state = new SymbState(TlaRex(NameEx("x")), arena, binding, solverCtx)
    new SymbStateRewriter().rewriteOnce(state, FastForward()) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$%d".format(cell.id))
        assert(TlaRex(expected) == nextState.rex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("FALSE \\/ TRUE ~~> TRUE") {
    val ex = OperEx(TlaBoolOper.or, ValEx(TlaFalse), ValEx(TlaTrue))
    val solverCtx = new Z3SolverContext()
    val state = new SymbState(TlaRex(ex), Arena.create(), new Binding, solverCtx)
    val finalState = new SymbStateRewriter().rewriteUntilDone(state)
    assert(PredRex(solverCtx.predTrue) == finalState.rex)
    assert(state.arena == finalState.arena)
  }

  test("FALSE \\/ (TRUE /\\ FALSE) ~~> FALSE") {
    val ex = OperEx(TlaBoolOper.or,
      ValEx(TlaFalse),
      OperEx(TlaBoolOper.and, ValEx(TlaTrue), ValEx(TlaFalse)))
    val solverCtx = new Z3SolverContext()
    val state = new SymbState(TlaRex(ex), Arena.create(), new Binding, solverCtx)
    val finalState = new SymbStateRewriter().rewriteUntilDone(state)
    assert(PredRex(solverCtx.predFalse) == finalState.rex)
    assert(state.arena == finalState.arena)
  }

  test("SE-BOOL-NEG1: ~(x \\/ y) ~~> ~x /\\ ~y") {
    val solverCtx = new Z3SolverContext()
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.or, NameEx("x"), NameEx("y")))
    val state = new SymbState(TlaRex(ex), Arena.create(), new Binding, solverCtx)
    new SymbStateRewriter().rewriteOnce(state, FastForward()) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.and,
          OperEx(TlaBoolOper.not, NameEx("x")),
          OperEx(TlaBoolOper.not, NameEx("y")))
        assert(TlaRex(expected) == nextState.rex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-NEG2: ~(x /\\ y) ~~> ~x \\/ ~y") {
    val solverCtx = new Z3SolverContext()
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.and, NameEx("x"), NameEx("y")))
    val state = new SymbState(TlaRex(ex), Arena.create(), new Binding, solverCtx)
    new SymbStateRewriter().rewriteOnce(state, FastForward()) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.or,
          OperEx(TlaBoolOper.not, NameEx("x")),
          OperEx(TlaBoolOper.not, NameEx("y")))
        assert(TlaRex(expected) == nextState.rex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")    }
  }

  test("SE-BOOL-NEG3: ~(x => y) ~~> x /\\ ~y") {
    val solverCtx = new Z3SolverContext()
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.implies, NameEx("x"), NameEx("y")))
    val state = new SymbState(TlaRex(ex), Arena.create(), new Binding, solverCtx)
    new SymbStateRewriter().rewriteOnce(state, FastForward()) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.and,
          NameEx("x"),
          OperEx(TlaBoolOper.not, NameEx("y")))
        assert(TlaRex(expected) == nextState.rex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")    }
  }

  test("SE-BOOL-NEG4: ~(x <=> y) ~~> ~x <=> y") {
    val solverCtx = new Z3SolverContext()
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.equiv, NameEx("x"), NameEx("y")))
    val state = new SymbState(TlaRex(ex), Arena.create(), new Binding, solverCtx)
    new SymbStateRewriter().rewriteOnce(state, FastForward()) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.equiv,
          OperEx(TlaBoolOper.not, NameEx("x")),
          NameEx("y"))
        assert(TlaRex(expected) == nextState.rex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")    }
  }

  test("SE-BOOL-NEG5: ~~x ~~> x") {
    val solverCtx = new Z3SolverContext()
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.not, NameEx("x")))
    val state = new SymbState(TlaRex(ex), Arena.create(), new Binding, solverCtx)
    new SymbStateRewriter().rewriteOnce(state, FastForward()) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(TlaRex(NameEx("x")) == nextState.rex)
        assert(state.arena == nextState.arena)
        assert(state.binding == nextState.binding)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-NEG6: ~\\E x \\in S: p ~~> \\A x \\in S: ~p") {
    val solverCtx = new Z3SolverContext()
    val ex = OperEx(TlaBoolOper.not,
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("S"), NameEx("p")))
    val state = new SymbState(TlaRex(ex), Arena.create(), new Binding, solverCtx)
    new SymbStateRewriter().rewriteOnce(state, FastForward()) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.forall, NameEx("x"), NameEx("S"),
          OperEx(TlaBoolOper.not, NameEx("p")))
        assert(TlaRex(expected) == nextState.rex)
        assert(state.arena == nextState.arena)
        assert(state.binding == nextState.binding)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-NEG7: ~\\A x \\in S: p ~~> \\E x \\in S: ~p") {
    val solverCtx = new Z3SolverContext()
    val ex = OperEx(TlaBoolOper.not,
      OperEx(TlaBoolOper.forall, NameEx("x"), NameEx("S"), NameEx("p")))
    val state = new SymbState(TlaRex(ex), Arena.create(), new Binding, solverCtx)
    new SymbStateRewriter().rewriteOnce(state, FastForward()) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("S"),
          OperEx(TlaBoolOper.not, NameEx("p")))
        assert(TlaRex(expected) == nextState.rex)
        assert(state.arena == nextState.arena)
        assert(state.binding == nextState.binding)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
