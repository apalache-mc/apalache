package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterFunSet extends RewriterBase {
  test("""SE-FUNSET1: [{1, 2, 3} ~~> {FALSE, TRUE}]""") {
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

  // bugfix 27/12/2017
  test("""SE-FUNSET1: [0..(5 - 1) ~~> {FALSE, TRUE}]""") {
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
