package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.BmcOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterFunSet extends RewriterBase {
  test("""SE-FUNSET1: [{1, 2, 3} -> {FALSE, TRUE}]""") {
    val domain = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val codomain = tla.enumSet(tla.bool(false), tla.bool(true))
    val state = new SymbState(tla.funSet(domain, codomain),
      CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(CellTheory().hasConst(name))
        val cell = nextState.arena.findCellByNameEx(nextState.ex)
        assert(cell.cellType == FinFunSetT(FinSetT(IntT()), FinSetT(BoolT())))
        val dom = nextState.arena.getDom(cell)
        assert(dom.cellType == FinSetT(IntT()))
        val domElems = nextState.arena.getHas(dom)
        assert(domElems.length == 3)
        val cdm = nextState.arena.getCdm(cell)
        assert(cdm.cellType == FinSetT(BoolT()))
        val cdmElems = nextState.arena.getHas(cdm)
        assert(cdmElems.length == 2)
      // the contents is tested in the rules below

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUNSET2: [{1, 2} -> Expand(SUBSET {FALSE, TRUE})]""") {
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = OperEx(BmcOper.expand,
      tla.powSet(tla.enumSet(tla.bool(false), tla.bool(true))))
    val state = new SymbState(tla.funSet(domain, codomain), CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(CellTheory().hasConst(name))
        val cell = nextState.arena.findCellByNameEx(nextState.ex)
        assert(cell.cellType == FinFunSetT(FinSetT(IntT()), FinSetT(FinSetT(BoolT()))))
        val dom = nextState.arena.getDom(cell)
        assert(dom.cellType == FinSetT(IntT()))
        val domElems = nextState.arena.getHas(dom)
        assert(domElems.length == 2)
        val cdm = nextState.arena.getCdm(cell)
        assert(cdm.cellType == FinSetT(FinSetT(BoolT())))

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // the existential over a function set should work without expanding the powerset!
  test("""SE-FUNSET2: Skolem(\E f \in [{1, 2} -> SUBSET {FALSE, TRUE}]: g' <- f)""") {
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.powSet(tla.enumSet(tla.bool(false), tla.bool(true)))
    val pred = tla.assignPrime(tla.name("g"), tla.name("f"))
    val exists =
      tla.exists(tla.name("f"), tla.funSet(domain, codomain), pred)
    val skolem = OperEx(BmcOper.skolem, exists)
    val state = new SymbState(skolem, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    val gprime = nextState.binding("g'")
    assert(FunT(FinSetT(IntT()), FinSetT(BoolT())) == gprime.cellType)
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  // the existential over a function set should work without expanding the powerset!
  test("""SE-FUNSET2: Skolem(\E f \in [{1, 2} -> SUBSET {FALSE}]: f[1] = {TRUE})""") {
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.powSet(tla.enumSet(tla.bool(false)))
    val pred = tla.eql(tla.appFun(tla.name("f"), tla.int(1)), tla.enumSet(tla.bool(true)))
    val exists =
      tla.exists(
        tla.name("f"),
        tla.funSet(domain, codomain),
        pred)
    val skolem = OperEx(BmcOper.skolem, exists)
    val state = new SymbState(skolem, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  // An existential over a function set that returns a function set to a powerset. Does it blow up your mind? :-)
  test("""SE-FUNSET2: Skolem(\E f \in [{1, 2} -> [{3} -> SUBSET {FALSE, TRUE}]]: g' <- f)""") {
    val domain1 = tla.enumSet(tla.int(1), tla.int(2))
    val domain2 = tla.enumSet(tla.int(3))
    val codomain2 = tla.powSet(tla.enumSet(tla.bool(false), tla.bool(true)))
    val codomain1 = tla.funSet(domain2, codomain2)
    val funset = tla.funSet(domain1, codomain1)
    val pred = tla.assignPrime(tla.name("g"), tla.name("f"))
    val exists =
      tla.exists(tla.name("f"), funset, pred)
    val skolem = OperEx(BmcOper.skolem, exists)
    val state = new SymbState(skolem, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    val gprime = nextState.binding("g'")
    assert(FunT(FinSetT(IntT()), FunT(FinSetT(IntT()), FinSetT(BoolT()))) == gprime.cellType)
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  // this should be fixed by implementing #91
  test("""SE-FUNSET2: [x \in {1, 2} |-> {x = 1}] \in [{1, 2} -> SUBSET {FALSE, TRUE}]""") {
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.powSet(tla.enumSet(tla.bool(false), tla.bool(true)))
    val funset = tla.funSet(domain, codomain)
    val fun = tla.funDef(tla.enumSet(tla.eql(tla.name("x"), tla.int(1))),
      tla.name("x"),
      domain)
    val state = new SymbState(tla.in(fun, funset), BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.push()
        solverContext.assertGroundExpr(nextState.ex)
        assert(solverContext.sat())
        solverContext.pop()
        solverContext.push()
        solverContext.assertGroundExpr(tla.not(nextState.ex))
        solverContext.pop()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-FUNSET2: [x \in {1, 2} |-> 3] \in [{1, 2} -> {3, 4}]""") {
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.enumSet(tla.int(3), tla.int(4))
    val funset = tla.funSet(domain, codomain)
    val fun = tla.funDef(tla.int(3),
      tla.name("x"),
      domain)
    val state = new SymbState(tla.in(fun, funset), BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  // this should be redundant in the presence of #91
  test("""SE-FUNSET2: [x \in {0, 1, 2} \ {0} |-> 3] \in [{1, 2} -> {3, 4}]""") {
    // although 0 is in the function domain at the arena level, it does not belong to the set difference
    def setminus(set: TlaEx, intVal: Int): TlaEx = {
      tla.filter(tla.name("t"),
        set,
        tla.not(tla.eql(tla.name("t"), tla.int(intVal))))
    }

    val domain1 = setminus(tla.enumSet(0.to(2).map(tla.int): _*), 0)
    val domain2 = tla.enumSet(1.to(2).map(tla.int): _*)
    val codomain = tla.enumSet(tla.int(3), tla.int(4))
    val funset = tla.funSet(domain2, codomain)
    val fun = tla.funDef(tla.int(3),
      tla.name("x"),
      domain1)
    val state = new SymbState(tla.in(fun, funset), BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  // this should be fixed by implementing #91
  test("""SE-FUNSET2: [x \in {1, 2} |-> {TRUE}] \in [{1, 2} -> SUBSET {FALSE}]""") {
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.powSet(tla.enumSet(tla.bool(false)))
    val funset = tla.funSet(domain, codomain)
    val fun = tla.funDef(tla.enumSet(tla.bool(true)),
      tla.name("x"),
      domain)
    val state = new SymbState(tla.in(fun, funset), BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.not(nextState.ex)))
  }

  // this should be fixed by implementing #91
  test("""SE-FUNSET with a SUBSET: [x \in {1, 2} |-> {TRUE}] \in [{1, 2} -> SUBSET {FALSE, TRUE}]""") {
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.powSet(tla.enumSet(tla.bool(false), tla.bool(true)))
    val funset = tla.funSet(domain, codomain)
    val fun = tla.funDef(tla.enumSet(tla.bool(true)),
      tla.name("x"),
      domain)
    val state = new SymbState(tla.in(fun, funset), BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  // bugfix 27/12/2017
  test("""SE-FUNSET1: [0..(5 - 1) -> {FALSE, TRUE}]""") {
    val domain = tla.dotdot(tla.int(0), tla.minus(tla.int(5), tla.int(1)))
    val codomain = tla.enumSet(tla.bool(false), tla.bool(true))
    val state = new SymbState(tla.funSet(domain, codomain),
      CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(CellTheory().hasConst(name))
        val cell = nextState.arena.findCellByNameEx(nextState.ex)
        assert(cell.cellType == FinFunSetT(FinSetT(IntT()), FinSetT(BoolT())))
        val dom = nextState.arena.getDom(cell)
        assert(dom.cellType == FinSetT(IntT()))
        val domElems = nextState.arena.getHas(dom)
        assert(domElems.length == 5)
        val cdm = nextState.arena.getCdm(cell)
        assert(cdm.cellType == FinSetT(BoolT()))
        val cdmElems = nextState.arena.getHas(cdm)
        assert(cdmElems.length == 2)
      // the contents is tested in the rules below

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
