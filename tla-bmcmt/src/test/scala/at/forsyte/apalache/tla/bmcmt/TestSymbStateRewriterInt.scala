package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir.{IntT1, NameEx}
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterInt extends RewriterBase {
  test("$C$_i: Int = $C$_j: Int") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightCell = arena.topCell
    val eq1 = tla.eql(cellEx(leftCell), cellEx(rightCell))
    val state = new SymbState(eq1, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        assert(solverContext.sat())
        val eq2 = tla.eql(cellEx(leftCell), tla.int(22))
        solverContext.assertGroundExpr(eq2)
        rewriter.push()
        val eq3 = tla.eql(cellEx(rightCell), tla.int(22))
        solverContext.assertGroundExpr(eq3)
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(tla.unchecked(predEx)))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        val eq4 = tla.eql(cellEx(rightCell), tla.int(1981))
        solverContext.assertGroundExpr(eq4)
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(tla.unchecked(predEx)))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int = $Z$j ~~> $B$k") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftInt = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightInt = arena.topCell
    val state = new SymbState(tla.eql(cellEx(leftInt), cellEx(rightInt)), arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(tla.eql(cellEx(leftInt), tla.int(22)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightInt), tla.int(22)))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(tla.unchecked(predEx)))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightInt), tla.int(1981)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(tla.unchecked(predEx)))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
  test("$C$_i: Int < $C$_j: Int ~~> valInt(...) < valInt(...)") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightCell = arena.topCell
    val state =
      new SymbState(tla.lt(cellEx(leftCell), cellEx(rightCell)), arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(tla.eql(cellEx(leftCell), tla.int(4)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(22)))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(4)))
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(3)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$C$_i: Int <= $C$_j: Int ~~> valInt(...) <= valInt(...)") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightCell = arena.topCell
    val state =
      new SymbState(tla.le(cellEx(leftCell), cellEx(rightCell)), arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(tla.eql(cellEx(leftCell), tla.int(4)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(22)))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(4)))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(3)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$C$_i: Int > $C$_j: Int ~~> valInt(...) > valInt(...)") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightCell = arena.topCell
    val state =
      new SymbState(tla.gt(cellEx(leftCell), cellEx(rightCell)), arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(tla.eql(cellEx(leftCell), tla.int(4)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(22)))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(4)))
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(3)))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("(composite expressions): 1 + 5 > 6 - 3 ~~> $B$_k") { rewriterType: SMTEncoding =>
    val left = tla.plus(tla.int(1), tla.int(5))
    val right = tla.minus(tla.int(6), tla.int(3))
    val state = new SymbState(tla.gt(left, right), arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(_) =>
        assert(solverContext.sat())
        rewriter.push()
        solverContext.assertGroundExpr(cmpEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(tla.unchecked(cmpEx)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$C$_i: Int >= $C$_j: Int ~~> valInt(...) >= valInt(...)") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftCell = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightCell = arena.topCell
    val state =
      new SymbState(tla.ge(cellEx(leftCell), cellEx(rightCell)), arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case cmpEx @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(cmpEx)
        solverContext.assertGroundExpr(tla.eql(cellEx(leftCell), tla.int(4)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(22)))
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(4)))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightCell), tla.int(3)))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("~($Z$Int = $Z$j) ~~> $B$k") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftInt = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightInt = arena.topCell
    val state =
      new SymbState(tla.not(tla.eql(cellEx(leftInt), cellEx(rightInt))), arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(tla.eql(cellEx(leftInt), tla.int(22)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightInt), tla.int(22)))
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(tla.unchecked(predEx)))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.pop()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightInt), tla.int(1981)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(tla.unchecked(predEx)))
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int + $Z$j ~~> $Z$k") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftInt = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightInt = arena.topCell
    val expr = tla.plus(cellEx(leftInt), cellEx(rightInt))
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(tla.eql(cellEx(leftInt), tla.int(1981)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightInt), tla.int(36)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(2017)))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(2016)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int - $Z$j ~~> $Z$k") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftInt = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightInt = arena.topCell
    val expr = tla.minus(cellEx(leftInt), cellEx(rightInt))
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(tla.eql(cellEx(leftInt), tla.int(2017)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightInt), tla.int(36)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(1981)))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(1980)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("-$Z$j ~~> $Z$k") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftInt = arena.topCell
    val expr = tla.uminus(cellEx(leftInt))
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(tla.eql(cellEx(leftInt), tla.int(2017)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(-2017)))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(2017)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int * $Z$j ~~> $Z$k") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftInt = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightInt = arena.topCell
    val expr = tla.mult(cellEx(leftInt), cellEx(rightInt))
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(tla.eql(cellEx(leftInt), tla.int(7)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightInt), tla.int(4)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(28)))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(30)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int / $Z$j ~~> $Z$k") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftInt = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightInt = arena.topCell
    val expr = tla.div(cellEx(leftInt), cellEx(rightInt))
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(tla.eql(cellEx(leftInt), tla.int(30)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightInt), tla.int(4)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(7)))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(8)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("$Z$Int % $Z$j ~~> $Z$k") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(IntT1)
    val leftInt = arena.topCell
    arena = arena.appendCell(IntT1)
    val rightInt = arena.topCell
    val expr = tla.mod(cellEx(leftInt), cellEx(rightInt))
    val state = new SymbState(expr, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(_) =>
        assert(solverContext.sat())
        solverContext.assertGroundExpr(tla.eql(cellEx(leftInt), tla.int(30)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(cellEx(rightInt), tla.int(7)))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(2)))
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.unchecked(result), tla.int(1)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2..5  = {2, 3, 4, 5}""") { rewriterType: SMTEncoding =>
    val expected = tla.enumSet(2.until(6).map(i => tla.int(i)): _*)
    val range = tla.dotdot(tla.int(2), tla.int(5))
    val eqExpected = tla.eql(range, expected)

    val state = new SymbState(eqExpected, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        assert(solverContext.sat())
        // check equality
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(tla.unchecked(predEx)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-INT-RNG: 2..(6 - 1)  = {2, 3, 4, 5}""") { rewriterType: SMTEncoding =>
    val expected = tla.enumSet(2.to(5).map(i => tla.int(i)): _*)
    val range = tla.dotdot(tla.int(2), tla.minus(tla.int(6), tla.int(1)))
    val eqExpected = tla.eql(range, expected)

    val state = new SymbState(eqExpected, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        assert(solverContext.sat())
        // check equality
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        val notPred = tla.not(tla.unchecked(predEx))
        solverContext.assertGroundExpr(notPred)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

}
