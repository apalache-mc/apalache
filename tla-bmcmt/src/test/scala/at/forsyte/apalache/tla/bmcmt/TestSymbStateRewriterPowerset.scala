package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.rules.aux.PowSetCtor
import at.forsyte.apalache.tla.bmcmt.types.{CellTFrom, PowSetT}
import at.forsyte.apalache.tla.lir.{IntT1, NameEx, SetT1}
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterPowerset extends RewriterBase {
  test("""SUBSET {1, 2, 3}""") { rewriterType: SMTEncoding =>
    val ex = tla.powSet(tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        val cell = nextState.arena.findCellByNameEx(nextState.ex)
        assert(cell.cellType == PowSetT(SetT1(IntT1)))
        val dom = nextState.arena.getDom(cell)
        assert(dom.cellType == CellTFrom(SetT1(IntT1)))
        val domElems = nextState.arena.getHas(dom)
        assert(domElems.length == 3)
      // the contents is tested in the rules below

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET1: {1, 2} \in SUBSET {1, 2, 3}""") { rewriterType: SMTEncoding =>
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val powset = tla.powSet(tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    val inEx = tla.in(set12, powset)
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SE-SUBSET1: {} \in SUBSET {1, 2, 3}""") { rewriterType: SMTEncoding =>
    // an empty set requires a type annotation
    val emptySet = tla.emptySet(IntT1)
    val powset = tla.powSet(tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    val inEx = tla.in(emptySet, powset)
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SE-SUBSET1: {1, 2, 3} \in SUBSET {1, 2, 3}""") { rewriterType: SMTEncoding =>
    val set1to3 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val powset = tla.powSet(set1to3)
    val inEx = tla.in(set1to3, powset)
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SE-SUBSET1: {1, 2, 3, 4} \in SUBSET {1, 2, 3}""") { rewriterType: SMTEncoding =>
    def setTo(k: Int) = tla.enumSet((1 to k).map(i => tla.int(i)): _*)

    val set1to4 = setTo(4)
    val powset = tla.powSet(setTo(3))
    val inEx = tla.not(tla.in(set1to4, powset))
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SSE-SUBSETEQ: {1, 2, 3, 4} \in SUBSET Nat""") { rewriterType: SMTEncoding =>
    def setTo(k: Int) = tla.enumSet((1 to k).map(i => tla.int(i)): _*)

    val set1to4 = setTo(4)
    val powset = tla.powSet(tla.natSet())
    val inEx = tla.in(set1to4, powset)
    val state = new SymbState(inEx, arena, Binding())

    val rewriter = create(rewriterType)
    try {
      val _ = rewriter.rewriteUntilDone(state)
      fail("expected an error message about subseteq over infinite sets being unsupported")
    } catch {
      case _: RewriterException => () // OK
    }
  }

  test("""SSE-SUBSETEQ: Nat \in SUBSET {1, 2, 3, 4}""") { rewriterType: SMTEncoding =>
    def setTo(k: Int) = tla.enumSet((1 to k).map(i => tla.int(i)): _*)

    val set1to4 = setTo(4)
    val powset = tla.powSet(set1to4)
    val nat = tla.natSet()
    val inEx = tla.in(nat, powset)
    val state = new SymbState(inEx, arena, Binding())

    val rewriter = create(rewriterType)
    try {
      val _ = rewriter.rewriteUntilDone(state)
      fail("expected an error message about subseteq over infinite sets being unsupported")
    } catch {
      case _: RewriterException => () // OK
    }
  }

  test("""SSE-SUBSETEQ: Nat \in SUBSET Nat""") { rewriterType: SMTEncoding =>
    val nat = tla.natSet()
    val powset = tla.powSet(tla.natSet())
    val inEx = tla.in(nat, powset)
    val state = new SymbState(inEx, arena, Binding())

    val rewriter = create(rewriterType)
    try {
      val _ = rewriter.rewriteUntilDone(state)
      fail("expected an error message about subseteq over infinite sets being unsupported")
    } catch {
      case _: RewriterException => () // OK
    }
  }

  test("""SSE-SUBSETEQ: Nat \in SUBSET Int""") { rewriterType: SMTEncoding =>
    val nat = tla.natSet()
    val powset = tla.powSet(tla.intSet())
    val inEx = tla.in(nat, powset)
    val state = new SymbState(inEx, arena, Binding())

    val rewriter = create(rewriterType)
    try {
      val _ = rewriter.rewriteUntilDone(state)
      fail("expected an error message about subseteq over infinite sets being unsupported")
    } catch {
      case _: RewriterException => () // OK
    }
  }

  test("""SSE-SUBSETEQ: Int \in SUBSET Nat""") { rewriterType: SMTEncoding =>
    val nat = tla.intSet()
    val powset = tla.powSet(tla.natSet())
    val inEx = tla.in(nat, powset)
    val state = new SymbState(inEx, arena, Binding())

    val rewriter = create(rewriterType)
    try {
      val _ = rewriter.rewriteUntilDone(state)
      fail("expected an error message about subseteq over infinite sets being unsupported")
    } catch {
      case _: RewriterException => () // OK
    }
  }

  test("""SE-SUBSET: \E X \in SUBSET {1, 2}: TRUE (sat)""") { rewriterType: SMTEncoding =>
    // a regression test that failed in the previous versions
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val ex = tla.exists(tla.name("X", SetT1(IntT1)), tla.powSet(set), tla.bool(true))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    try {
      val _ = rewriter.rewriteUntilDone(state)
      fail("expected an error message about unfolding a powerset")
    } catch {
      case _: UnsupportedOperationException => () // OK
    }
  }

  test("""SE-SUBSET: Skolem(\E X \in SUBSET {1, 2}: TRUE) (sat)""") { rewriterType: SMTEncoding =>
    // a regression test that failed in the previous versions
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val ex =
      tla.skolem(tla.exists(tla.name("X", SetT1(IntT1)), tla.powSet(set), tla.bool(true)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET: Skolem(\E X \in SUBSET {1, 2}: FALSE (unsat))""") { rewriterType: SMTEncoding =>
    // a regression test that failed in the previous versions
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val ex =
      tla.skolem(tla.exists(tla.name("X", SetT1(IntT1)), tla.powSet(set), tla.bool(false)))

    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""PowSetCtor {1, 2}""") { rewriterType: SMTEncoding =>
    val baseset = tla.enumSet(tla.int(1), tla.int(2))
    val state = new SymbState(baseset, arena, Binding())
    val rewriter = create(rewriterType)
    var nextState = rewriter.rewriteUntilDone(state)
    val baseCell = nextState.asCell
    nextState = new PowSetCtor(rewriter).confringo(nextState, baseCell)
    // check equality
    val eq = tla.eql(tla.unchecked(nextState.ex),
        tla.enumSet(
            tla.emptySet(IntT1),
            tla.enumSet(tla.int(1)),
            tla.enumSet(tla.int(2)),
            tla.enumSet(tla.int(1), tla.int(2)),
        ))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

}
