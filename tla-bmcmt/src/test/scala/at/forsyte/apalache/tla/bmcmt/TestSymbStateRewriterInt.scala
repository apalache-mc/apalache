package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.IntT
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, NameEx, SetT1}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterInt extends RewriterBase {
  private val Int = IntT1()
  private val Bool = BoolT1()
  private val IntSet = SetT1(IntT1())

  test("$C$_i: Int = $C$_j: Int") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val eq1 = eql(leftCell.toNameEx as Int, rightCell.toNameEx as Int) as Bool
    val state = new SymbState(eq1, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        assert(solverContext.sat())
        val eq2 = eql(leftCell.toNameEx as Int, int(22)) as Bool
        solverContext.assertGroundExpr(eq2)
        rewriter.push()
        val eq3 = eql(rightCell.toNameEx as Int, int(22)) as Bool
        solverContext.assertGroundExpr(eq3)
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as Bool) as Bool)
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        val eq4 = eql(rightCell.toNameEx as Int, int((1981))) as Bool
        solverContext.assertGroundExpr(eq4)
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as Bool) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int = $Z$j ~~> $B$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val state = new SymbState(eql(leftInt as Int, rightInt as Int) as Bool, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt as Int, int(22)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt as Int, int(22)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as Bool) as Bool)
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightInt as Int, int((1981))) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as Bool) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
  test("$C$_i: Int < $C$_j: Int ~~> valInt(...) < valInt(...)") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val state =
      new SymbState(lt(leftCell.toNameEx as Int, rightCell.toNameEx as Int) as Bool, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(eql(leftCell.toNameEx as Int, int(4)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(22)) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(4)) as Bool)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(3)) as Bool)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$C$_i: Int <= $C$_j: Int ~~> valInt(...) <= valInt(...)") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val state =
      new SymbState(le(leftCell.toNameEx as Int, rightCell.toNameEx as Int) as Bool, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(eql(leftCell.toNameEx as Int, int(4)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(22)) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(4)) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(3)) as Bool)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$C$_i: Int > $C$_j: Int ~~> valInt(...) > valInt(...)") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val state =
      new SymbState(gt(leftCell.toNameEx as Int, rightCell.toNameEx as Int) as Bool, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(eql(leftCell.toNameEx as Int, int(4)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(22)) as Bool)
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(4)) as Bool)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(3)) as Bool)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("(composite expressions): 1 + 5 > 6 - 3 ~~> $B$_k") {
    val left = plus(int(1), int(5)).typed(IntT1())
    val right = minus(int(6), int(3)).typed(IntT1())
    val state = new SymbState(gt(left, right).typed(BoolT1()), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(name) =>
        assert(solverContext.sat())
        rewriter.push()
        solverContext.assertGroundExpr(cmpEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(cmpEx as Bool) as Bool)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$C$_i: Int >= $C$_j: Int ~~> valInt(...) >= valInt(...)") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val state =
      new SymbState(ge(leftCell.toNameEx as Int, rightCell.toNameEx as Int) as Bool, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(eql(leftCell.toNameEx as Int, int(4)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(22)) as Bool)
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(4)) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx as Int, int(3)) as Bool)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("~($Z$Int = $Z$j) ~~> $B$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val state =
      new SymbState(not(eql(leftInt as Int, rightInt as Int) as Bool) as Bool, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt as Int, int(22)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt as Int, int(22)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as Bool) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightInt as Int, int(1981)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as Bool) as Bool)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int + $Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val expr = plus(leftInt as Int, rightInt as Int) as Int
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt as Int, int(1981)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt as Int, int(36)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(2017)) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(2016)) as Bool)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int - $Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val expr = minus(leftInt as Int, rightInt as Int) as Int
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt as Int, int(2017)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt as Int, int(36)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(1981)) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(1980)) as Bool)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("-$Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    val expr = uminus(leftInt as Int) as Int
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt as Int, int(2017)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(-2017)) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(2017)) as Bool)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int * $Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val expr = mult(leftInt as Int, rightInt as Int) as Int
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt as Int, int(7)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt as Int, int(4)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(28)) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(30)) as Bool)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int / $Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val expr = div(leftInt as Int, rightInt as Int) as Int
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt as Int, int(30)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt as Int, int(4)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(7)) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(8)) as Bool)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int % $Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val expr = mod(leftInt as Int, rightInt as Int) as Int
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt as Int, int(30)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt as Int, int(7)) as Bool)
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(2)) as Bool)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result as Int, int(1)) as Bool)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2..5  = {2, 3, 4, 5}""") {
    val expected = enumSet(2.until(6).map(int): _*).typed(SetT1(IntT1()))
    val range = dotdot(int(2), int(5)).typed(SetT1(IntT1()))
    val eqExpected = eql(range, expected).typed(BoolT1())

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
        solverContext.assertGroundExpr(not(predEx as Bool) as Bool)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-INT-RNG: 2..(6 - 1)  = {2, 3, 4, 5}""") {
    val expected = enumSet(2.to(5).map(int): _*).typed(SetT1(IntT1()))
    val range = dotdot(int(2), minus(int(6), int(1)) as Int) as IntSet
    val eqExpected = eql(range, expected).typed(BoolT1())

    val state = new SymbState(eqExpected, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        assert(solverContext.sat())
        // check equality
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        val notPred = not(predEx as Bool) as Bool
        solverContext.assertGroundExpr(notPred)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

}
