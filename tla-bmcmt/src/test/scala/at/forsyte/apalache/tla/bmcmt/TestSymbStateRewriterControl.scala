package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.smt.{PreproSolverContext, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.types.{FailPredT, IntT}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterControl extends RewriterBase with TestingPredefs {
  test("""SE-ITE[1-4]: IF 3 > 2 THEN 2 < 4 ELSE 5 < 1 ~~> $C$k""") {
    val pred = tla.gt(tla.int(3), tla.int(2))
    val e1 = tla.lt(tla.int(2), tla.int(4))
    val e2 = tla.lt(tla.int(5), tla.int(1))
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(res)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(res))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-ITE[1-4]: IF 3 < 2 THEN 2 < 4 ELSE 5 < 1 ~~> $C$k""") {
    val pred = tla.lt(tla.int(3), tla.int(2))
    val e1 = tla.lt(tla.int(2), tla.int(4))
    val e2 = tla.lt(tla.int(5), tla.int(1))
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(res))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(res)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-ITE[1-4]: IF 3 > 2 THEN 4 ELSE 1 ~~> $C$k""") {
    val pred = tla.gt(tla.int(3), tla.int(2))
    val e1 = tla.int(4)
    val e2 = tla.int(1)
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.int(4), res))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.eql(tla.int(1), res))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-ITE[1-4]: IF 3 < 2 THEN 4 ELSE 1 ~~> $C$k""") {
    val pred = tla.lt(tla.int(3), tla.int(2))
    val e1 = tla.int(4)
    val e2 = tla.int(1)
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.int(1), res))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.eql(tla.int(4), res))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-ITE[5]: IF 3 < 2 THEN {1, 2} ELSE {2, 3} ~~> {2, 3}""") {
    val pred = tla.lt(tla.int(3), tla.int(2))
    val e1 = tla.enumSet(tla.int(1), tla.int(2))
    val e2 = tla.enumSet(tla.int(2), tla.int(3))
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        assert(solverContext.sat())
        rewriter.push()
        val eqState = rewriter.rewriteUntilDone(nextState.setRex(tla.eql(res, e2)))
        solverContext.assertGroundExpr(eqState.ex)
        assert(solverContext.sat())
        rewriter.pop()
        val neqState = rewriter.rewriteUntilDone(nextState.setRex(tla.eql(res, e1)))
        solverContext.assertGroundExpr(neqState.ex)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }


  test("""SE-ITE[5]: IF 1 = 1 THEN {2} ELSE {1} ] ~~> $C$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val ite = tla.ite(tla.eql(1, 1), tla.enumSet(2), tla.enumSet(1))
    val eq = tla.eql(tla.enumSet(2), ite)

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(solverContext.sat())
        solverContext.push()
        solverContext.assertGroundExpr(tla.not(nextState.ex))
        assertUnsatOrExplain(rewriter, nextState)
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(nextState.ex)
        assert(solverContext.sat())
        solverContext.pop()


      case _ =>
        fail("Unexpected rewriting result")
    }
  }


  test("""SE-ITE[5]: IF 2 < 3 THEN {1, 2} ELSE {2, 3} ~~> {1, 2}""") {
    val pred = tla.lt(tla.int(2), tla.int(3))
    val e1 = tla.enumSet(tla.int(1), tla.int(2))
    val e2 = tla.enumSet(tla.int(2), tla.int(3))
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        assert(solverContext.sat())
        rewriter.push()
        val eqState = rewriter.rewriteUntilDone(nextState.setRex(tla.eql(res, e1)))
        solverContext.assertGroundExpr(eqState.ex)
        assert(solverContext.sat())
        rewriter.pop()
        val neqState = rewriter.rewriteUntilDone(nextState.setRex(tla.eql(res, e2)))
        solverContext.assertGroundExpr(neqState.ex)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-ITE[1-4]: 1 + (IF 3 < 2 THEN 4 ELSE 1) ~~> $C$k""") {
    val pred = tla.lt(tla.int(3), tla.int(2))
    val e1 = tla.int(4)
    val e2 = tla.int(1)
    val ite = tla.plus(tla.int(1), tla.ite(pred, e1, e2))

    val state = new SymbState(ite, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.int(2), res))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.eql(tla.int(5), res))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // LET-IN is often used to cache computation results
  test("""LET A == 1 + 2 IN 1 + A ~~> 4""") {
    val decl = TlaOperDecl("A", List(), tla.plus(1, 2))
    val letIn = tla.letIn(tla.plus(1, tla.appDecl(decl)), decl)
    val state = new SymbState(letIn, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(nextState.ex, tla.int(4))))
  }

  // handled by Keramelizer
  // CASE i = 1 -> 2 [] i = 2 -> 3 [] i = 3 -> 1]
  ignore("""SE-CASE1: CASE i = 1 -> 2 [] i = 2 -> 3 [] i = 3 -> 1]""") {
    def guard(arg: Int) = tla.eql("i", arg)

    val caseEx = tla.caseAny(guard(1), 2, guard(2), 3, guard(3), 1)

    def caseExEqConst(i: Int) = tla.eql(i, caseEx)

    for (i <- List(1, 2, 3)) {
      // reinitialize the arena and the solver
      solverContext = new PreproSolverContext(solverContext)
      arena = Arena.create(solverContext)
      arena = arena.appendCell(IntT())
      val icell = arena.topCell
      val binding = Binding("i" -> icell)
      val state = new SymbState(caseEx, arena, binding)
      val rewriter = create()
      val nextState = rewriter.rewriteUntilDone(state)
      nextState.ex match {
        case res@NameEx(name) =>
          rewriter.push()
          solverContext.assertGroundExpr(tla.eql(icell.toNameEx, i))
          solverContext.assertGroundExpr(tla.eql(1 + (i % 3), res))
          assert(solverContext.sat())
          rewriter.pop()
          rewriter.push()
          val failureOccurs = tla.or(nextState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
          solverContext.assertGroundExpr(failureOccurs)
          assert(solverContext.sat()) // this possible since there is no OTHER case and the constraints do not restrict us
          rewriter.pop()
          rewriter.push()
          solverContext.assertGroundExpr(tla.eql(icell.toNameEx, i))
          solverContext.assertGroundExpr(tla.not(failureOccurs))
          solverContext.assertGroundExpr(tla.eql(i, res))
          assert(!solverContext.sat())
          rewriter.pop()

        case _ =>
          fail("Unexpected rewriting result")
      }

      arena = nextState.arena // update the arena for the next iteration
    }
  }

  // handled by Keramelizer
  // CASE i = 1 -> 2 [] i = 2 -> 3 [] i = 3 -> 1 [] OTHER -> 4]
  ignore("""SE-CASE1: CASE i = 1 -> 2 [] i = 2 -> 3 [] i = 3 -> 1 [] OTHER -> 4]""") {
    def guard(arg: Int) = tla.eql("i", arg)
    val caseEx = tla.caseOther(4, guard(1), 2, guard(2), 3, guard(3), 1)
    def caseExEqConst(i: Int) = tla.eql(i, caseEx)

    for (i <- List(1, 2, 3, 99)) {
      // reinitialize the arena and the solver
      solverContext = new PreproSolverContext(solverContext)
      arena = Arena.create(solverContext)
      arena = arena.appendCell(IntT())
      val icell = arena.topCell
      val binding = Binding("i" -> icell)
      val state = new SymbState(caseEx, arena, binding)
      val rewriter = create()
      val nextState = rewriter.rewriteUntilDone(state)
      nextState.ex match {
        case res @ NameEx(name) =>
          rewriter.push()
          solverContext.assertGroundExpr(tla.eql(icell.toNameEx, i))
          val expectedValue = if (i <= 3) 1 + (i % 3) else 4
          solverContext.assertGroundExpr(tla.eql(expectedValue, res))
          assert(solverContext.sat())
          rewriter.pop()
          rewriter.push()
          val failureOccurs = tla.or(nextState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
          solverContext.assertGroundExpr(failureOccurs)
          assert(!solverContext.sat()) // no failure should occur, as there is the OTHER case
          rewriter.pop()
          rewriter.push()
          solverContext.assertGroundExpr(tla.eql(icell.toNameEx, i))
          solverContext.assertGroundExpr(tla.not(failureOccurs))
          solverContext.assertGroundExpr(tla.eql(i, res))
          assert(!solverContext.sat())
          rewriter.pop()

        case _ =>
          fail("Unexpected rewriting result")
      }

      arena = nextState.arena // update the arena for the next iteration
    }

  }

}
