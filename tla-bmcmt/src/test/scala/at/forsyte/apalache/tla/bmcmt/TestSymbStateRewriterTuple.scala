package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterTuple extends RewriterBase {
  test("""SE-TUPLE-CTOR[1-2]: <<1, FALSE, {2}>> ~~> $C$k""") {
    val tuple = TlaFunOper.mkTuple(tla.int(1), tla.bool(false), tla.enumSet(tla.int(2)))

    val state = new SymbState(tuple, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter(solverContext).rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case TupleT(List(IntT(), BoolT(), FinSetT(IntT()))) =>
            () // OK

            // we check the actual contents in the later tests that access elements

          case _ =>
            fail("Unexpected type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  /*
  test("""SE-TPL-ACC[1-2]: <<1, FALSE, {2}>>[2] ~~> $C$k equals FALSE""") {
    val tuple = tla.tuple(tla.int(1), tla.bool(false), tla.enumSet(tla.int(2)))
    val tupleAcc = tla.appFun(tuple, tla.int(2))
    val state = new SymbState(tuple, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
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

  test("""SE-FUN-APP[1-3]: f[4] ~~> $C$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val mapping = OperEx(TlaArithOper.mult, NameEx("x"), ValEx(TlaInt(3)))
    val fun = OperEx(TlaFunOper.funDef, mapping, NameEx("x"), set)
    val app = OperEx(TlaFunOper.app, fun, ValEx(TlaInt(4)))

    val state = new SymbState(app, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case IntT() =>
            solverContext.push()
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, cell.toNameEx, ValEx(TlaInt(12))))
            assert(solverContext.sat())
            solverContext.pop()
            solverContext.assertGroundExpr(OperEx(TlaOper.ne, cell.toNameEx, ValEx(TlaInt(12))))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
  */
}
