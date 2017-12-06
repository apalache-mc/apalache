package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{FinSetT, FunT, IntT}
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterFun extends RewriterBase {
  test("""SE-FUN-CTOR[1-2]: [x \in {1,2,3,4} |-> x / 3: ] ~~> $C$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3)), ValEx(TlaInt(4)))
    val mapping = OperEx(TlaArithOper.div, NameEx("x"), ValEx(TlaInt(3)))
    val fun = OperEx(TlaFunOper.funDef, mapping, NameEx("x"), set)

    val state = new SymbState(fun, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case FunT(FinSetT(IntT()), IntT()) =>
            () // OK

          case _ =>
            fail("Unexpected type")
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
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, cell.toNameEx, ValEx(TlaInt(12))))
            solverContext.push()
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

  test("""SE-FUN-APP[1-3]: [x \in {1, 2} |-> x][4] ~~> $C$failure""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(2)))
    val mapping = NameEx("x")
    val fun = OperEx(TlaFunOper.funDef, mapping, NameEx("x"), set)
    val app = OperEx(TlaFunOper.app, fun, ValEx(TlaInt(4)))

    val state = new SymbState(app, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        solverContext.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, membershipEx, arena.cellFailure().toNameEx))
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.ne, membershipEx, arena.cellFailure().toNameEx))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  /* TODO: implement it in the future


  test("""SE-FUN-UPD[1-4]: [[x \in {1, 2} |-> 2 * x] EXCEPT ![1] = 11] ~~> $C$fun""") {
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val mapExpr = tla.mult(tla.int(2), tla.name("x"))
    val fun = tla.funDef(mapExpr, tla.name("x"), set)

    val except = tla.except(fun, tla.int(1), tla.int(11))
    val state = new SymbState(except, CellTheory(), arena, new Binding, solverContext)
    val nextState = new SymbStateRewriter().rewriteUntilDone(state)
    nextState.ex match {
      case resFunEx @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        // check the function domain and co-domain
        val resFun = nextState.arena.findCellByName(name)
        val dom = nextState.arena.getDom(resFun)
        val cdm = nextState.arena.getCdm(resFun)
        assert(nextState.arena.getHas(dom).size == 2)
        val cdmSize = nextState.arena.getHas(cdm).size
        assert(cdmSize == 2 || cdmSize == 3) // the co-domain can be overapproximated

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
  */
}
