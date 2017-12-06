package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaInt
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriter extends RewriterBase {
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
}