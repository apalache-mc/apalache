package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.analyses.FreeExistentialsStoreImpl
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.plugins.Identifier
import at.forsyte.apalache.tla.lir.predef.TlaBoolSet
import at.forsyte.apalache.tla.lir.values.TlaInt
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner


@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterFun extends RewriterBase with TestingPredefs {
  test("""SE-FUN-CTOR[1-2]: [x \in {1,2,3,4} |-> x / 3: ] ~~> $C$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(tla.int(1), tla.int(2), tla.int(3), tla.int(4))
    val mapping = OperEx(TlaArithOper.div, NameEx("x"), tla.int(3))
    val fun = OperEx(TlaFunOper.funDef, mapping, NameEx("x"), set)

    val state = new SymbState(fun, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
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

  test("""SE-FUN-CTOR[1-2]: [x \in {1,2,3} |-> IF x = 1 THEN {2} ELSE IF x = 2 THEN {3} ELSE {1} ] ~~> $C$k""") {
    val set = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    def intSet(i: Int) = tla.enumSet(tla.int(i))
    val mapping = tla.ite(
      tla.eql(tla.name("x"), tla.int(1)),
      intSet(2),
      tla.ite(tla.eql(tla.name("x"), tla.int(2)),
        intSet(3),
        intSet(1))
    )////
    val fun = tla.funDef(mapping, tla.name("x"), set)

    val state = new SymbState(fun, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUN-CTOR[1-2]: [x \in {1,2} |-> {} ][1] = {} ~~> $C$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(tla.int(1), tla.int(2))
    val mapping = tla.enumSet()
    val fun = OperEx(TlaFunOper.funDef, mapping, NameEx("x"), set)
    val eq = tla.eql(tla.appFun(fun, tla.int(1)), tla.enumSet())

    val state = new SymbState(eq, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case result @ NameEx(name) =>
        solverContext.push()
        solverContext.assertGroundExpr(result)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(tla.not(result))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUN-CTOR[1-2]: [x \in {1,2} |-> IF x = 1 THEN {2} ELSE {1} ][1] ~~> $C$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = tla.enumSet(1, 2)
    val mapping = tla.ite(tla.eql("x", 1), tla.enumSet(2), tla.enumSet(1))
    val fun = tla.funDef(mapping, "x", set)
    val eq = tla.eql(tla.enumSet(2), tla.appFun(fun, 1))

    val state = new SymbState(eq, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val failureOccurs = tla.or(nextState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        assert(solverContext.sat())
        solverContext.push()
        solverContext.assertGroundExpr(nextState.ex)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(tla.not(nextState.ex))
        assert(!solverContext.sat())
        solverContext.pop()


      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // regression: this test did not work with EWD840
  test("""SE-FUN-CTOR[1-2]: [x \in {1,2} |-> ["a" |-> x] ][1] ~~> $C$k""") {
    val set = tla.enumSet(1, 2)
    val mapping = tla.enumFun(tla.str("a"), tla.name("x"))
    val fun = tla.funDef(mapping, "x", set)
    val eq = tla.eql(tla.enumFun(tla.str("a"), 1), tla.appFun(fun, 1))

    val state = new SymbState(eq, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val failureOccurs = tla.or(nextState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        assert(solverContext.sat())
        solverContext.push()
        solverContext.assertGroundExpr(nextState.ex)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(tla.not(nextState.ex))
        assert(!solverContext.sat())
        solverContext.pop()


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

    val state = new SymbState(app, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case IntT() =>
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, cell.toNameEx, ValEx(TlaInt(12))))
            rewriter.push()
            assert(solverContext.sat())
            rewriter.pop()
            solverContext.assertGroundExpr(OperEx(TlaOper.ne, cell.toNameEx, ValEx(TlaInt(12))))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUN-APP[1-3]: [x \in {1, 2} |-> x][4] ~~> failure!""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = mkSet(ValEx(TlaInt(1)), ValEx(TlaInt(2)))
    val mapping = NameEx("x")
    val fun = OperEx(TlaFunOper.funDef, mapping, NameEx("x"), set)
    val app = OperEx(TlaFunOper.app, fun, ValEx(TlaInt(4)))

    val state = new SymbState(app, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        // In the previous version, we were using failure predicates to detect failures.
        // However, they were an unnecessary burden and produced tonnes of constraints.
        // In the new version, we just return some value,
        // which is similar to Leslie's interpretation.
        // The most important thing is that the SMT context is still satisfiable.
        assert(solverContext.sat())
        /*
        // the code with failure predicates
        rewriter.push()
        val failureOccurs = tla.or(nextState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(failureOccurs)
        assert(solverContext.sat())
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        assert(!solverContext.sat())
        */

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUN-APP[1-3]: [x \in {3} |-> {1, x}][3] ~~> $C$k""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val set = tla.enumSet(tla.int(3))
    val mapping = tla.enumSet(tla.int(1), tla.name("x"))
    val fun = tla.funDef(mapping, tla.name("x"), set)
    val app = OperEx(TlaFunOper.app, fun, tla.int(3))

    val state = new SymbState(app, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case FinSetT(IntT()) =>
            () // type OK, check equality below

          case _ =>
            fail("Unexpected type")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
    rewriter.push()
    val appEq = tla.eql(nextState.ex, tla.enumSet(tla.int(1), tla.int(3)))
    val eqState = nextState.setRex(appEq).setTheory(BoolTheory())
    create().rewriteUntilDone(eqState).ex match {
      case eqEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.assertGroundExpr(eqEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
    rewriter.pop()
    val appNeq = tla.neql(nextState.ex, tla.enumSet(tla.int(1), tla.int(3)))
    val neqState = nextState.setRex(appNeq).setTheory(BoolTheory())
    rewriter.rewriteUntilDone(neqState).ex match {
      case eqEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.assertGroundExpr(eqEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUN-EQ4: [y \in BOOLEAN |-> ~y] = [x \in BOOLEAN |-> ~x]""") {
    val fun1 = tla.funDef(tla.not(tla.name("y")), tla.name("y"), ValEx(TlaBoolSet))
    val fun2 = tla.funDef(tla.not(tla.name("x")), tla.name("x"), ValEx(TlaBoolSet))
    val state = new SymbState(tla.eql(fun1, fun2), BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(membershipEx))
        val failureOccurs = tla.or(nextState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUN-NE: [y \in BOOLEAN |-> ~y] /= [x \in BOOLEAN |-> ~x]""") {
    val fun1 = tla.funDef(tla.not(tla.name("y")), tla.name("y"), ValEx(TlaBoolSet))
    val fun2 = tla.funDef(tla.not(tla.name("x")), tla.name("x"), ValEx(TlaBoolSet))
    val state = new SymbState(tla.neql(fun1, fun2), BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        val failureOccurs = tla.or(nextState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(membershipEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUN-NE: [y \in BOOLEAN |-> ~y] /= [x \in BOOLEAN |-> x]""") {
    val fun1 = tla.funDef(tla.not(tla.name("y")), tla.name("y"), ValEx(TlaBoolSet))
    val fun2 = tla.funDef(tla.name("x"), tla.name("x"), ValEx(TlaBoolSet))
    val state = new SymbState(tla.neql(fun1, fun2), BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        val failureOccurs = tla.or(nextState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        val isSat = solverContext.sat()
        assert(isSat)
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(membershipEx))
        val isUnsat = !solverContext.sat()
        assert(isUnsat)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // a function returning a function
  test("""SE-FUN-APP[1-3]: [x \in {3} |-> [y \in BOOLEAN |-> ~y]][3] ~~> $C$k""") {
    val set = tla.enumSet(tla.int(3))
    val boolNegFun = tla.funDef(tla.not(tla.name("y")), tla.name("y"), ValEx(TlaBoolSet))

    val fun = tla.funDef(boolNegFun, tla.name("x"), set)
    val app = OperEx(TlaFunOper.app, fun, tla.int(3))

    val state = new SymbState(app, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        cell.cellType match {
          case FunT(FinSetT(BoolT()), BoolT()) =>
            () // type OK, check equality below

          case _ =>
            fail("Unexpected type: " + cell.cellType)
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
    rewriter.push()
    val appEq = tla.eql(nextState.ex, boolNegFun)
    val eqState = rewriter.rewriteUntilDone(nextState.setRex(appEq).setTheory(BoolTheory()))
    eqState.ex match {
      case eqEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.assertGroundExpr(eqEx)
        val isSat = solverContext.sat()
        assert(isSat)

      case _ =>
        fail("Unexpected rewriting result")
    }
    rewriter.pop()
    rewriter.push()
    val appNeq = tla.neql(nextState.ex, boolNegFun)
    val neqState = rewriter.rewriteUntilDone(nextState.setRex(appNeq).setTheory(BoolTheory()))
    neqState.ex match {
      case neqEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.assertGroundExpr(neqEx)
        val failureOccurs = tla.or(neqState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        assertUnsatOrExplain(rewriter, neqState)

      case _ =>
        fail("Unexpected rewriting result")
    }
    rewriter.pop()
  }

  test("""SE-FUN-APP[1-4]: [x \in {1, 2} |-> IF x = 1 THEN 11 ELSE 2 * x][1] ~~> $C$fun""") {
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val pred = tla.eql(tla.name("x"), tla.int(1))
    val ite = tla.ite(pred, tla.int(11), tla.mult(tla.int(2), tla.name("x")))
    val iteFun = tla.funDef(ite, tla.name("x"), set)
    val iteFunElem = tla.appFun(iteFun, tla.int(1))
    val iteFunElemNe11 = tla.neql(iteFunElem, tla.int(11))

    val state = new SymbState(iteFunElemNe11, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case resFunEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.assertGroundExpr(resFunEx)
        val failureOccurs = tla.or(nextState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        val isSat = solverContext.sat()
        assert(!isSat)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUN-UPD[1-4]: [[x \in {1, 2} |-> 2 * x] EXCEPT ![1] = 11] ~~> $C$fun""") {
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val mapExpr = tla.mult(tla.int(2), tla.name("x"))
    val fun = tla.funDef(mapExpr, tla.name("x"), set)

    val except = tla.except(fun, tla.tuple(tla.int(1)), tla.int(11))
    val state = new SymbState(except, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case resFunEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        // check the function domain and co-domain
        val resFun = nextState.asCell
        // no domain anymore
//        val dom = nextState.arena.getDom(resFun)
//        assert(nextState.arena.getHas(dom).size == 2)
        val cdm = nextState.arena.getCdm(resFun)
        val cdmSize = nextState.arena.getHas(cdm).size
        assert(cdmSize == 2 || cdmSize == 3) // the co-domain can be overapproximated

      case _ =>
        fail("Unexpected rewriting result")
    }

    val exceptFun = nextState.asCell

    val resFun1Ne11 = tla.neql(tla.appFun(nextState.ex, tla.int(1)), tla.int(11))
    val cmpState = rewriter.rewriteUntilDone(nextState.setRex(resFun1Ne11).setTheory(BoolTheory()))

    // compare
    rewriter.push()

    // make sure that not equals gives us sat
    cmpState.ex match {
      case neqEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.assertGroundExpr(neqEx)
        /*
        // not using failure predicates anymore
        val failureOccurs = tla.or(cmpState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        */
        assertUnsatOrExplain(rewriter, cmpState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // In general, the index is a tuple; tla-import gives us a singleton tuple.
  test("""SE-FUN-UPD[1-4]: [[x \in {1, 2} |-> 2 * x] EXCEPT ![(1)] = 11] ~~> $C$fun""") {
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val mapExpr = tla.mult(tla.int(2), tla.name("x"))
    val fun = tla.funDef(mapExpr, tla.name("x"), set)

    val except = tla.except(fun, tla.tuple(tla.int(1)), tla.int(11))
    val state = new SymbState(except, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case resFunEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        // check the function domain and co-domain
        val resFun = nextState.arena.findCellByName(name)
        // no domain anymore
//        val dom = nextState.arena.getDom(resFun)
//        assert(nextState.arena.getHas(dom).size == 2)
        val cdm = nextState.arena.getCdm(resFun)
        val cdmSize = nextState.arena.getHas(cdm).size
        assert(cdmSize == 2 || cdmSize == 3) // the co-domain can be overapproximated

      case _ =>
        fail("Unexpected rewriting result")
    }

    val exceptFun = nextState.arena.findCellByNameEx(nextState.ex)

    val resFun1Ne11 = tla.neql(tla.appFun(nextState.ex, tla.int(1)), tla.int(11))
    val cmpState = rewriter.rewriteUntilDone(nextState.setRex(resFun1Ne11).setTheory(BoolTheory()))

    // compare
    rewriter.push()

    // make sure that not equals gives us sat
    cmpState.ex match {
      case neqEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.assertGroundExpr(neqEx)
        val failureOccurs = tla.or(cmpState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        assertUnsatOrExplain(rewriter, cmpState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUN-UPD[1-4] and singleton tuple: [[x \in {1, 2} |-> 2 * x] EXCEPT ![(1)] = 11] ~~> $C$fun""") {
    // singleton tuples in EXCEPT are erased and converted into the tuple element
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val mapExpr = tla.mult(tla.int(2), tla.name("x"))
    val fun = tla.funDef(mapExpr, tla.name("x"), set)

    val except = tla.except(fun, tla.tuple(tla.int(1)), tla.int(11))
    val state = new SymbState(except, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case resFunEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        // check the function domain and co-domain
        val resFun = nextState.arena.findCellByName(name)
        // no domain anymore
//        val dom = nextState.arena.getDom(resFun)
//        assert(nextState.arena.getHas(dom).size == 2)
        val cdm = nextState.arena.getCdm(resFun)
        val cdmSize = nextState.arena.getHas(cdm).size
        assert(cdmSize == 2 || cdmSize == 3) // the co-domain can be overapproximated

      case _ =>
        fail("Unexpected rewriting result")
    }

    val exceptFun = nextState.arena.findCellByNameEx(nextState.ex)

    val resFun1Ne11 = tla.neql(tla.appFun(nextState.ex, tla.int(1)), tla.int(11))
    val cmpState = rewriter.rewriteUntilDone(nextState.setRex(resFun1Ne11).setTheory(BoolTheory()))

    // compare
    rewriter.push()

    // make sure that not equals gives us sat
    cmpState.ex match {
      case neqEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.assertGroundExpr(neqEx)
        val failureOccurs = tla.or(cmpState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        assertUnsatOrExplain(rewriter, cmpState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUN-UPD[1-4], singleton tuple, and const: [[x \in {"a", "b"} |-> 3] EXCEPT ![("a")] = 11] ~~> $C$fun""") {
    // singleton tuples in EXCEPT are erased and converted into the tuple element
    val set = tla.enumSet(tla.str("a"), tla.str("b"))
    val mapExpr = tla.int(3)
    val fun = tla.funDef(mapExpr, tla.name("x"), set)

    val except = tla.except(fun, tla.tuple(tla.str("a")), tla.int(11))
    val state = new SymbState(except, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case resFunEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        // check the function domain and co-domain
        val resFun = nextState.arena.findCellByName(name)
        // no domain anymore
//        val dom = nextState.arena.getDom(resFun)
//        assert(nextState.arena.getHas(dom).size == 2)
        val cdm = nextState.arena.getCdm(resFun)
        val cdmSize = nextState.arena.getHas(cdm).size
        assert(cdmSize == 2 || cdmSize == 3) // the co-domain can be overapproximated

      case _ =>
        fail("Unexpected rewriting result")
    }

    val exceptFun = nextState.arena.findCellByNameEx(nextState.ex)

    val resFun1Ne11 = tla.neql(tla.appFun(nextState.ex, tla.str("a")), tla.int(11))
    val cmpState = rewriter.rewriteUntilDone(nextState.setRex(resFun1Ne11).setTheory(BoolTheory()))

    // compare
    rewriter.push()

    // make sure that not equals gives us sat
    cmpState.ex match {
      case neqEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.assertGroundExpr(neqEx)
        val failureOccurs = tla.or(cmpState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        assertUnsatOrExplain(rewriter, cmpState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""fun in a set: \E x \in {[y \in BOOLEAN |-> ~y]}: x[FALSE]""") {
    // this test was failing in the buggy implementation with PICK .. FROM and FUN-MERGE
    val fun1 = tla.funDef(tla.not(tla.name("y")), tla.name("y"), ValEx(TlaBoolSet))
    val exists = tla.exists(tla.name("x"),
      tla.enumSet(fun1),
      tla.appFun(NameEx("x"), tla.bool(false)))

    // here, we have to overred FreeExistentialsStore, and thus cannot use SymbStateRewriterAuto
    val typeFinder = new TrivialTypeFinder()
    val rewriter = new SymbStateRewriterImpl(solverContext, typeFinder)
    val fex = new FreeExistentialsStoreImpl()
    Identifier.identify(exists)
    fex.store.add(exists.ID)
    rewriter.freeExistentialsStore = fex
    typeFinder.inferAndSave(exists)

    val state = new SymbState(exists, BoolTheory(), arena, new Binding)
    val nextState = rewriter.rewriteUntilDone(state)
    val failureOccurs = tla.or(nextState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
    solverContext.assertGroundExpr(tla.not(failureOccurs))
    assertTlaExAndRestore(rewriter, nextState)
    // check failure predicates
    solverContext.assertGroundExpr(nextState.ex)
    val failure = tla.or(nextState.arena.findCellsByType(FailPredT()).map(_.toNameEx): _*)
    solverContext.assertGroundExpr(failure)
    assert(!solverContext.sat())
  }

  test("""SE-FUN-DOMAIN: DOMAIN [x \in {1,2,3} |-> x / 2: ]""") {
    val set = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val mapping = OperEx(TlaArithOper.div, NameEx("x"), tla.int(2))
    val fun = tla.funDef(mapping, tla.name("x"), set)
    val dom = tla.dom(fun)
    val eq = tla.eql(dom, set)

    val rewriter = create()
    val state = new SymbState(eq, CellTheory(), arena, new Binding)
    assertTlaExAndRestore(rewriter, state)
  }

  // TrivialTypeFinder does not support let-in and operator declarations
  ignore("""SE-SET-APP[1-2]: LET X = {1, 2} \cap {2} IN [y \in X |-> TRUE][2] ~~> $B$k""") {
    // regression
    val fun = tla.funDef(tla.bool(true), "y", "Oper:X")
    val app = tla.appFun(fun, 2)
    val ex = tla.letIn(app,
      tla.declOp("X", tla.cap(tla.enumSet(1, 2), tla.enumSet(2))))

    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(solverContext.sat()) // it should be sat
        rewriter.push()
        val failPreds = nextState.arena.findCellsByType(FailPredT())
        val failureOccurs = tla.or(failPreds.map(_.toNameEx) :_*)
        solverContext.assertGroundExpr(tla.not(failureOccurs))
        assert(solverContext.sat()) // no deadlock

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

}
