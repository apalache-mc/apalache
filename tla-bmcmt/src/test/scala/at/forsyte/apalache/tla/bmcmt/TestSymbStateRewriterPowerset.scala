package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.rules.aux.PowSetCtor
import at.forsyte.apalache.tla.bmcmt.types.{CellTFrom, PowSetT}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.values.{TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, NameEx, SetT1, Typed, ValEx}

trait TestSymbStateRewriterPowerset extends RewriterBase {
  private val types = Map(
      "i" -> IntT1,
      "I" -> SetT1(IntT1),
      "II" -> SetT1(SetT1(IntT1)),
      "b" -> BoolT1,
  )

  test("""SUBSET {1, 2, 3}""") { rewriterType: SMTEncoding =>
    val ex = powSet(enumSet(int(1), int(2), int(3)) ? "I")
      .typed(types, "II")
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
    val set12 = enumSet(int(1), int(2)) ? "I"
    val powset = powSet(enumSet(int(1), int(2), int(3)) ? "I") ? "II"
    val inEx = in(set12, powset)
      .typed(types, "b")
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SE-SUBSET1: {} \in SUBSET {1, 2, 3}""") { rewriterType: SMTEncoding =>
    // an empty set requires a type annotation
    val emptySet = enumSet()
      .typed(types, "I")
    val powset = powSet(enumSet(int(1), int(2), int(3)) ? "I") ? "II"
    val inEx = in(emptySet, powset)
      .typed(types, "b")
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SE-SUBSET1: {1, 2, 3} \in SUBSET {1, 2, 3}""") { rewriterType: SMTEncoding =>
    val set1to3 = enumSet(int(1), int(2), int(3)) ? "I"
    val powset = powSet(set1to3) ? "II"
    val inEx = in(set1to3, powset)
      .typed(types, "b")
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SE-SUBSET1: {1, 2, 3, 4} \in SUBSET {1, 2, 3}""") { rewriterType: SMTEncoding =>
    def setTo(k: Int) = enumSet((1 to k).map(int): _*)

    val set1to4 = setTo(4) ? "I"
    val powset = powSet(setTo(3) ? "I") ? "II"
    val inEx = not(in(set1to4, powset) ? "b")
      .typed(types, "b")
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SSE-SUBSETEQ: {1, 2, 3, 4} \in SUBSET Nat""") { rewriterType: SMTEncoding =>
    def setTo(k: Int) = enumSet((1 to k).map(int): _*)

    val set1to4 = setTo(4) ? "I"
    val powset = powSet(ValEx(TlaNatSet)(Typed(SetT1(IntT1)))) ? "II"
    val inEx = in(set1to4, powset)
      .typed(types, "b")
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
    def setTo(k: Int) = enumSet((1 to k).map(int): _*)

    val set1to4 = setTo(4) ? "I"
    val powset = powSet(set1to4) ? "II"
    val nat = ValEx(TlaNatSet)(Typed(SetT1(IntT1))) ? "I"
    val inEx = in(nat, powset)
      .typed(types, "b")
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
    val nat = ValEx(TlaNatSet)(Typed(SetT1(IntT1))) ? "I"
    val powset = powSet(ValEx(TlaNatSet)(Typed(SetT1(IntT1)))) ? "II"
    val inEx = in(nat, powset)
      .typed(types, "b")
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
    val nat = ValEx(TlaNatSet)(Typed(SetT1(IntT1))) ? "I"
    val powset = powSet(ValEx(TlaIntSet)(Typed(SetT1(IntT1)))) ? "II"
    val inEx = in(nat, powset)
      .typed(types, "b")
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
    val nat = ValEx(TlaIntSet)(Typed(SetT1(IntT1))) ? "I"
    val powset = powSet(ValEx(TlaNatSet)(Typed(SetT1(IntT1)))) ? "II"
    val inEx = in(nat, powset)
      .typed(types, "b")
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
    val set = enumSet(int(1), int(2)) ? "I"
    val ex = exists(name("X") ? "I", powSet(set) ? "II", bool(true))
      .typed(types, "b")
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
    val set = enumSet(int(1), int(2)) ? "I"
    val ex =
      apalacheSkolem(exists(name("X") ? "I", powSet(set) ? "II", bool(true)) ? "b")
        .typed(types, "b")
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
    val set = enumSet(int(1), int(2)) ? "I"
    val ex =
      apalacheSkolem(exists(name("X") ? "I", powSet(set) ? "II", bool(false)) ? "b")
        .typed(types, "b")

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
    val baseset = enumSet(int(1), int(2))
      .typed(types, "I")
    val state = new SymbState(baseset, arena, Binding())
    val rewriter = create(rewriterType)
    var nextState = rewriter.rewriteUntilDone(state)
    val baseCell = nextState.asCell
    nextState = new PowSetCtor(rewriter).confringo(nextState, baseCell)
    // check equality
    val eq = eql(nextState.ex,
        enumSet(enumSet() ? "I", enumSet(int(1)) ? "I", enumSet(int(2)) ? "I", enumSet(int(1), int(2)) ? "I") ? "II")
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

}
