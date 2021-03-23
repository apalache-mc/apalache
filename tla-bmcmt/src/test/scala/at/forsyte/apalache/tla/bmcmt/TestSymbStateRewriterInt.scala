package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.IntT
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, NameEx, SetT1}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterInt extends RewriterBase {
  private val intTypes = Map("i" -> IntT1(), "I" -> SetT1(IntT1()), "b" -> BoolT1())

  test("$C$_i: Int = $C$_j: Int") {
    arena = arena.appendCell(IntT())
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT())
    val rightCell = arena.topCell
    val eq1 = eql(leftCell.toNameEx ? "i", rightCell.toNameEx ? "i")
      .typed(intTypes, "b")
    val state = new SymbState(eq1, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        assert(solverContext.sat())
        val eq2 = eql(leftCell.toNameEx ? "i", int((22)))
          .typed(intTypes, "b")
        solverContext.assertGroundExpr(eq2)
        rewriter.push()
        val eq3 = eql(rightCell.toNameEx ? "i", int(22))
          .typed(intTypes, "b")
        solverContext.assertGroundExpr(eq3)
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(intTypes, "b"))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        val eq4 = eql(rightCell.toNameEx ? "i", int((1981))).typed(intTypes, "b")
        solverContext.assertGroundExpr(eq4)
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$i = $Z$j ~~> $B$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val state = new SymbState(eql(leftInt ? "i", rightInt ? "i").typed(intTypes, "b"), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt ? "i", int(22)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt ? "i", int(22)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(intTypes, "b"))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightInt ? "i", int((1981))).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(intTypes, "b"))
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
      new SymbState(lt(leftCell.toNameEx ? "i", rightCell.toNameEx ? "i").typed(intTypes, "b"), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(eql(leftCell.toNameEx ? "i", int(4)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(22)).typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(4)).typed(intTypes, "b"))
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(3)).typed(intTypes, "b"))
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
      new SymbState(le(leftCell.toNameEx ? "i", rightCell.toNameEx ? "i").typed(intTypes, "b"), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(eql(leftCell.toNameEx ? "i", int(4)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(22)).typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(4)).typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(3)).typed(intTypes, "b"))
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
      new SymbState(gt(leftCell.toNameEx ? "i", rightCell.toNameEx ? "i").typed(intTypes, "b"), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(eql(leftCell.toNameEx ? "i", int(4)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(22)).typed(intTypes, "b"))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(4)).typed(intTypes, "b"))
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(3)).typed(intTypes, "b"))
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
        solverContext.assertGroundExpr(not(cmpEx ? "b").typed(intTypes, "b"))
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
      new SymbState(ge(leftCell.toNameEx ? "i", rightCell.toNameEx ? "i").typed(intTypes, "b"), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(eql(leftCell.toNameEx ? "i", int(4)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(22)).typed(intTypes, "b"))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(4)).typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightCell.toNameEx ? "i", int(3)).typed(intTypes, "b"))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("~($Z$i = $Z$j) ~~> $B$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val state =
      new SymbState(not(eql(leftInt ? "i", rightInt ? "i") ? "b").typed(intTypes, "b"), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt ? "i", int(22)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt ? "i", int(22)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not((predEx ? "b")).typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        solverContext.assertGroundExpr(eql(rightInt ? "i", int(1981)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx ? "b").typed(intTypes, "b"))
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$i + $Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val expr = plus(leftInt ? "i", rightInt ? "i").typed(intTypes, "i")
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt ? "i", int(1981)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt ? "i", int(36)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(2017)).typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(2016)).typed(intTypes, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$i - $Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val expr = minus(leftInt ? "i", rightInt ? "i").typed(intTypes, "i")
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt ? "i", int(2017)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt ? "i", int(36)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(1981)).typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(1980)).typed(intTypes, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("-$Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    val expr = uminus(leftInt ? "i").typed(intTypes, "i")
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt ? "i", int(2017)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(-2017)).typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(2017)).typed(intTypes, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$i * $Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val expr = mult(leftInt ? "i", rightInt ? "i").typed(intTypes, "i")
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt ? "i", int(7)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt ? "i", int(4)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(28)).typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(30)).typed(intTypes, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$i / $Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val expr = div(leftInt ? "i", rightInt ? "i").typed(intTypes, "i")
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt ? "i", int(30)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt ? "i", int(4)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(7)).typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(8)).typed(intTypes, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$i % $Z$j ~~> $Z$k") {
    arena = arena.appendCell(IntT())
    val leftInt = arena.topCell.toNameEx
    arena = arena.appendCell(IntT())
    val rightInt = arena.topCell.toNameEx
    val expr = mod(leftInt ? "i", rightInt ? "i").typed(intTypes, "i")
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(eql(leftInt ? "i", int(30)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(rightInt ? "i", int(7)).typed(intTypes, "b"))
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(2)).typed(intTypes, "b"))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(eql(result ? "i", int(1)).typed(intTypes, "b"))
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
        solverContext.assertGroundExpr(not(predEx ? "b").typed(intTypes, "b"))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-INT-RNG: 2..(6 - 1)  = {2, 3, 4, 5}""") {
    val expected = enumSet(2.to(5).map(int): _*).typed(SetT1(IntT1()))
    val range = dotdot(int(2), minus(int(6), int(1)) ? "i")
      .typed(intTypes, "I")
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
        val notPred = not(predEx ? "b").typed(intTypes, "b")
        solverContext.assertGroundExpr(notPred)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

}
