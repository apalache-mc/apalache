package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterTuple extends RewriterBase {
  test("""SE-TUPLE-CTOR[1-2]: <<1, FALSE, {2}>> ~~> $C$k""") {
    val tuple = TlaFunOper.mkTuple(tla.int(1), tla.bool(false), tla.enumSet(tla.int(2)))

    val state = new SymbState(tuple, arena, Binding())
    val nextState = create().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        assert(TupleT(List(IntT(), BoolT(), FinSetT(IntT()))) == cell.cellType)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-TPL-ACC[1-2]: <<1, FALSE, {2}>>[2] ~~> $C$k equals FALSE""") {
    val tuple = tla.tuple(tla.int(1), tla.bool(false), tla.enumSet(tla.int(2)))
    val tupleAcc = tla.appFun(tuple, tla.int(2))
    val state = new SymbState(tupleAcc, arena, Binding())
    val nextState = create().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case BoolT() =>
            assert(solverContext.sat())
            solverContext.push()
            solverContext.assertGroundExpr(tla.eql(cell.toNameEx, tla.bool(false)))
            assert(solverContext.sat())
            solverContext.pop()
            solverContext.assertGroundExpr(tla.eql(cell.toNameEx, tla.bool(true)))
            assert(!solverContext.sat())

            // we check the actual contents in the later tests that access elements

          case _ =>
            fail("Expected Boolean type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-TUPLE-CTOR[1-2] in a set: {<<1, FALSE>>, <<2, TRUE>>} ~~> $C$k""") {
    val tuple1 = TlaFunOper.mkTuple(tla.int(1), tla.bool(false))
    val tuple2 = TlaFunOper.mkTuple(tla.int(2), tla.bool(true))

    val state = new SymbState(tla.enumSet(tuple1, tuple2), arena, Binding())
    val nextState = create().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        assert(FinSetT(TupleT(List(IntT(), BoolT()))) == cell.cellType)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""type inference error: {<<1, FALSE>>, <<2>>}""") {
    val tuple1 = TlaFunOper.mkTuple(tla.int(1), tla.bool(false))
    val tuple2 = TlaFunOper.mkTuple(tla.int(2))

    val state = new SymbState(tla.enumSet(tuple1, tuple2), arena, Binding())
    assertThrows[TypeInferenceException] {
      create().rewriteUntilDone(state)
      fail("Expected a type error")
    }
  }

  test("""type inference error: {<<1, FALSE>>, <<TRUE, 2>>} ~~> $C$k""") {
    val tuple1 = TlaFunOper.mkTuple(tla.int(1), tla.bool(false))
    val tuple2 = TlaFunOper.mkTuple(tla.bool(true), tla.int(2))

    val state = new SymbState(tla.enumSet(tuple1, tuple2), arena, Binding())
    assertThrows[TypeInferenceException] {
      create().rewriteUntilDone(state)
    }
  }

  test("""SE-TUPLE-EQ: ~(<<2, FALSE>> = <<2, TRUE>>) ~~> $C$k""") {
    val tuple1 = TlaFunOper.mkTuple(tla.int(2), tla.bool(false))
    val tuple2 = TlaFunOper.mkTuple(tla.int(2), tla.bool(true))
    val eq = tla.not(tla.eql(tuple1, tuple2))

    val rewriter = create()
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-TUPLE-EQ: <<2, FALSE>> = <<2, FALSE>> ~~> $C$k""") {
    val tuple1 = TlaFunOper.mkTuple(tla.int(2), tla.bool(false))
    val tuple2 = TlaFunOper.mkTuple(tla.int(2), tla.bool(false))
    val eq = tla.eql(tuple1, tuple2)

    val rewriter = create()
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  // Keramelizer rewrites \X
  ignore("""SE-TUPLE-SET: {<<1, FALSE>>, <<2, FALSE>>, <<1, TRUE>>, <<2, TRUE>> = {1,2} \X  {FALSE, TRUE} ~~> $B$k""") {
    val set12 = tla.enumSet(1 to 2 map tla.int :_*)
    val setBool = tla.enumSet(tla.bool(false), tla.bool(true))
    val prod = tla.times(set12, setBool)
    def tup(i: Int, b: Boolean) = tla.tuple(tla.int(i), tla.bool(b))
    val eq = tla.eql(prod, tla.enumSet(tup(1, false), tup(1, true), tup(2, false), tup(2, true)))

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assert(!solverContext.sat())
  }

  test("""SE-TUPLE-DOM: DOMAIN <<2, FALSE>> = {1, 2}""") {
    val tuple = TlaFunOper.mkTuple(tla.int(2), tla.bool(false), tla.str("c"))
    val set123 = tla.enumSet(1.to(3) map tla.int :_*)
    val eq = tla.eql(tla.dom(tuple), set123)
    val state = new SymbState(eq, arena, Binding())
    val rewriter = create()
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-TUPLE-EXCEPT: [ <<1, FALSE>> EXCEPT ![1] = 3 ]""") {
    val tuple = tla.tuple(tla.int(1), tla.bool(false))
    val except = tla.except(tuple, tla.tuple(tla.int(1)), tla.int(3))
    val state = new SymbState(except, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    val expectedTuple = tla.tuple(tla.int(3), tla.bool(false))
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(expectedTuple, nextState.ex)))
  }
}
