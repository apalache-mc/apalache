package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.IntT
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterInt extends RewriterBase {
  test("SE-INT-CELL-EQ1: $C$_i: Int = $C$_j: Int ~~> valInt(...) = valInt(...)") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val state = new SymbState(OperEx(TlaOper.eq, leftCell.toNameEx, rightCell.toNameEx),
      BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, leftCell.toNameEx, ValEx(TlaInt(22))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(22))))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(1981))))
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

  test("SE-INT-EQ1: $Z$i = $Z$j ~~> $B$k") {
    val leftInt = solverContext.introIntConst()
    val rightInt = solverContext.introIntConst()
    val state = new SymbState(OperEx(TlaOper.eq, NameEx(leftInt), NameEx(rightInt)),
      BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(22))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(22))))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(1981))))
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
  test("SE-INT-CELL-CMP1: $C$_i: Int < $C$_j: Int ~~> valInt(...) < valInt(...)") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val state = new SymbState(OperEx(TlaArithOper.lt, leftCell.toNameEx, rightCell.toNameEx),
      BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, leftCell.toNameEx, ValEx(TlaInt(4))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(22))))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(4))))
        assert(!solverContext.sat())
        rewriter.pop()
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
      BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, leftCell.toNameEx, ValEx(TlaInt(4))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(22))))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(4))))
        assert(solverContext.sat())
        rewriter.pop()
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
      BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, leftCell.toNameEx, ValEx(TlaInt(4))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(22))))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(4))))
        assert(!solverContext.sat())
        rewriter.pop()
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
      BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        rewriter.push()
        solverContext.assertGroundExpr(cmpEx)
        assert(solverContext.sat())
        rewriter.pop()
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
      BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, leftCell.toNameEx, ValEx(TlaInt(4))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(22))))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, rightCell.toNameEx, ValEx(TlaInt(4))))
        assert(solverContext.sat())
        rewriter.pop()
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
      BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(BoolTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(22))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(22))))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(1981))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, predEx))
        assert(!solverContext.sat())
        rewriter.pop()
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
    val state = new SymbState(expr, IntTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(1981))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(36))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(2017))))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
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
    val state = new SymbState(expr, IntTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(2017))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(36))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(1981))))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(1980))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-ARITH1[-.]: -$Z$j ~~> $Z$k") {
    val leftInt = solverContext.introIntConst()
    val expr = OperEx(TlaArithOper.uminus, NameEx(leftInt))
    val state = new SymbState(expr, IntTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(2017))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(-2017))))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(2017))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-INT-ARITH1[*]: $Z$i * $Z$j ~~> $Z$k") {
    val leftInt = solverContext.introIntConst()
    val rightInt = solverContext.introIntConst()
    val expr = OperEx(TlaArithOper.mult, NameEx(leftInt), NameEx(rightInt))
    val state = new SymbState(expr, IntTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(7))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(4))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(28))))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
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
    val state = new SymbState(expr, IntTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(30))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(4))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(7))))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
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
    val state = new SymbState(expr, IntTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        assert(IntTheory() == state.theory)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(leftInt), ValEx(TlaInt(30))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, NameEx(rightInt), ValEx(TlaInt(7))))
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(2))))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, result, ValEx(TlaInt(1))))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-INT-RNG: 2..5  = {2, 3, 4, 5}""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val expected = mkSet(Range(2, 6).map(i => ValEx(TlaInt(i))): _*)
    val range = OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(5)))
    val eqExpected = OperEx(TlaOper.eq, range, expected)

    val state = new SymbState(eqExpected, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
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

  test("""SE-INT-RNG: 2..(6 - 1)  = {2, 3, 4, 5}""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val expected = mkSet(Range(2, 6).map(i => tla.int(i)): _*)
    val range = tla.dotdot(tla.int(2), tla.minus(tla.int(6), tla.int(1)))
    val eqExpected = tla.eql(range, expected)

    val state = new SymbState(eqExpected, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
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

}
