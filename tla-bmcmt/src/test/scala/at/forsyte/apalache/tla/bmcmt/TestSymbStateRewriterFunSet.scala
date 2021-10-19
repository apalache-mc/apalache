package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterFunSet extends RewriterBase {
  val types =
    Map(
        "b" -> BoolT1(),
        "B" -> SetT1(BoolT1()),
        "BB" -> SetT1(SetT1(BoolT1())),
        "i" -> IntT1(),
        "I" -> SetT1(IntT1()),
        "(i)" -> TupT1(IntT1()),
        "i_to_i" -> FunT1(IntT1(), IntT1()),
        "i_to_I" -> FunT1(IntT1(), SetT1(IntT1())),
        "i_TO_i" -> SetT1(FunT1(IntT1(), IntT1())),
        "r" -> RecT1("a" -> IntT1()),
        "s" -> StrT1(),
        "S" -> SetT1(StrT1()),
        "(s)" -> TupT1(StrT1()),
        "i_to_s" -> FunT1(StrT1(), IntT1()),
        "s_to_i" -> FunT1(IntT1(), StrT1()),
        "i_to_r" -> FunT1(IntT1(), RecT1("a" -> IntT1())),
        "b_to_b" -> FunT1(BoolT1(), BoolT1()),
        "b_TO_b" -> SetT1(FunT1(BoolT1(), BoolT1())),
        "i_to_b" -> FunT1(IntT1(), BoolT1()),
        "i_to_B" -> FunT1(IntT1(), SetT1(BoolT1())),
        "i_TO_B" -> FunT1(IntT1(), SetT1(BoolT1())),
        "i_TO_i_to_B" -> SetT1(FunT1(IntT1(), FunT1(IntT1(), SetT1(BoolT1())))),
        "i_to_i_to_B" -> FunT1(IntT1(), FunT1(IntT1(), SetT1(BoolT1()))),
        "i_to_b_to_b" -> FunT1(IntT1(), FunT1(BoolT1(), BoolT1()))
    )

  test("""[{1, 2, 3} -> {FALSE, TRUE}]""") { rewriterType: String =>
    val domain = enumSet(int(1), int(2), int(3))
    val codomain = enumSet(bool(false), bool(true))
    val fs = funSet(domain ? "I", codomain ? "B")
      .typed(types, "i_to_b")
    val state = new SymbState(fs, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
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

  test("""[{1, 2} -> Expand(SUBSET {FALSE, TRUE})]""") { rewriterType: String =>
    val domain = enumSet(int(1), int(2))
    val codomain = apalacheExpand(powSet(enumSet(bool(false), bool(true)) ? "B") ? "BB")
    val fs = funSet(domain ? "I", codomain ? "BB")
      .typed(types, "i_to_B")

    val state = new SymbState(fs, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
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
  test("""Skolem(\E f \in [{1, 2} -> SUBSET {FALSE, TRUE}]: g' <- f)""") { rewriterType: String =>
    val domain = enumSet(int(1), int(2)) ? "I"
    val codomain = powSet(enumSet(bool(false), bool(true)) ? "B") ? "BB"
    val pred = assign(prime(name("g") ? "i_to_B") ? "i_to_B", name("f") ? "i_to_B")
      .typed(types, "b")
    val existsForm =
      exists(name("f") ? "i_to_B", funSet(domain, codomain) ? "i_to_B", pred)
        .typed(types, "b")
    val skolem = apalacheSkolem(existsForm)
      .typed(BoolT1())
    val state = new SymbState(skolem, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val gprime = nextState.binding("g'")
    assert(FunT(FinSetT(IntT()), FinSetT(BoolT())) == gprime.cellType)
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  // the existential over a function set should work without expanding the powerset!
  test("""Skolem(\E f \in [{1, 2} -> SUBSET {FALSE}]: f[1] = {TRUE})""") { rewriterType: String =>
    val domain = enumSet(int(1), int(2)) ? "I"
    val codomain = powSet(enumSet(bool(false)) ? "B") ? "BB"
    val pred = eql(appFun(name("f") ? "i_to_B", int(1)) ? "B", enumSet(bool(true)) ? "B")
      .typed(types, "b")
    val existsForm =
      exists(name("f") ? "i_to_B", funSet(domain, codomain) ? "i_TO_B", pred)
    val skolem = apalacheSkolem(existsForm ? "b")
      .typed(types, "b")
    val state = new SymbState(skolem, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  // An existential over a function set that returns a function set to a powerset. Does it blow up your mind? :-)
  test("""Skolem(\E f \in [{1, 2} -> [{3} -> SUBSET {FALSE, TRUE}]]: g' <- f)""") { rewriterType: String =>
    val domain1 = enumSet(int(1), int(2))
    val domain2 = enumSet(int(3))
    val codomain2 = powSet(enumSet(bool(false), bool(true)) ? "B") ? "BB"
    val codomain1 = funSet(domain2 ? "I", codomain2) ? "i_TO_B"
    val funset = funSet(domain1 ? "I", codomain1)
      .typed(types, "i_TO_i_to_B")
    val pred = assign(prime(name("g") ? "i_to_i_to_B") ? "i_to_i_to_B", name("f") ? "i_to_i_to_B")
      .typed(types, "b")
    val existsForm =
      exists(name("f") ? "i_to_i_to_B", funset ? "i_TO_i_to_B", pred)
        .typed(types, "b")
    val skolem = apalacheSkolem(existsForm)
      .typed(types, "b")
    val state = new SymbState(skolem, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val gprime = nextState.binding("g'")
    assert(FunT(FinSetT(IntT()), FunT(FinSetT(IntT()), FinSetT(BoolT()))) == gprime.cellType)
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  // this should be fixed by implementing #91
  test("""[x \in {1, 2} |-> {x = 1}] \in [{1, 2} -> SUBSET {FALSE, TRUE}]""") { rewriterType: String =>
    val domain = enumSet(int(1), int(2)) ? "I"
    val codomain = powSet(enumSet(bool(false), bool(true)) ? "B") ? "BB"
    val funset = funSet(domain, codomain) ? "i_to_B"
    val fun = funDef(enumSet(eql(name("x") ? "i", int(1)) ? "b") ? "B", name("x") ? "i", domain)
      .typed(types, "i_to_B")
    val funInFunSet = in(fun, funset)
      .typed(types, "b")
    val state = new SymbState(funInFunSet, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""[x \in {1, 2} |-> 3] \in [{1, 2} -> {3, 4}]""") { rewriterType: String =>
    val domain = enumSet(int(1), int(2)) ? "I"
    val codomain = enumSet(int(3), int(4)) ? "I"
    val funset = funSet(domain, codomain) ? "i_TO_i"
    val fun = funDef(int(3), name("x") ? "i", domain)
      .typed(types, "i_to_i")
    val funInFunSet = in(fun, funset)
      .typed(types, "b")
    val state = new SymbState(funInFunSet, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  // this should be redundant in the presence of #91
  test("""[x \in {0, 1, 2} \ {0} |-> 3] \in [{1, 2} -> {3, 4}]""") { rewriterType: String =>
    // although 0 is in the function domain at the arena level, it does not belong to the set difference
    def setminus(set: TlaEx, intVal: Int): TlaEx = {
      filter(name("t") ? "i", set, not(eql(name("t") ? "i", int(intVal)) ? "b") ? "b")
        .typed(types, "I")
    }

    val domain1 = setminus(
        enumSet(0.to(2).map(int): _*)
          .typed(types, "I"), 0)
    val domain2 = enumSet(1.to(2).map(int): _*)
      .typed(types, "I")
    val codomain = enumSet(int(3), int(4))
      .typed(types, "I")
    val funset = funSet(domain2, codomain)
      .typed(types, "i_TO_i")
    val fun = funDef(int(3), name("x") ? "i", domain1)
      .typed(types, "i_to_i")
    val funInFunSet = in(fun, funset)
      .typed(types, "b")

    val state = new SymbState(funInFunSet, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  // this should be fixed by implementing #91
  test("""[x \in {1, 2} |-> {TRUE}] \in [{1, 2} -> SUBSET {FALSE}]""") { rewriterType: String =>
    val domain = enumSet(int(1), int(2)) ? "I"
    val codomain = powSet(enumSet(bool(false)) ? "B") ? "BB"
    val funset = funSet(domain, codomain)
      .typed(types, "i_TO_B")
    val fun = funDef(enumSet(bool(true)) ? "B", name("x") ? "i", domain)
      .typed(types, "i_to_B")
    val funInFunSet = in(fun, funset)
      .typed(types, "b")

    val state = new SymbState(funInFunSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  // this should be fixed by implementing #91
  test("""[x \in {1, 2} |-> {TRUE}] \in [{1, 2} -> SUBSET {FALSE, TRUE}]""") { rewriterType: String =>
    val domain = enumSet(int(1), int(2)) ? "I"
    val codomain = powSet(enumSet(bool(false), bool(true)) ? "B") ? "BB"
    val funset = funSet(domain, codomain)
      .typed(types, "i_TO_B")
    val fun = funDef(enumSet(bool(true)) ? "B", name("x") ? "i", domain)
      .typed(types, "i_to_B")
    val funInFunSet = in(fun, funset)
      .typed(types, "b")
    val state = new SymbState(funInFunSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  // bugfix 27/12/2017
  test("""SE-FUNSET1: [0..(5 - 1) -> {FALSE, TRUE}]""") { rewriterType: String =>
    val domain = dotdot(int(0), minus(int(5), int(1)) ? "i") ? "I"
    val codomain = enumSet(bool(false), bool(true)) ? "B"
    val fs = funSet(domain, codomain)
      .typed(types, "i_to_b")
    val state = new SymbState(fs, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
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
