package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla._

trait TestSymbStateRewriterFunSet extends RewriterBase {
  val i_to_B: TlaType1 = FunT1(IntT1, SetT1(BoolT1))
  val i_to_i_to_B: TlaType1 = FunT1(IntT1, FunT1(IntT1, SetT1(BoolT1)))

  test("""[{1, 2, 3} -> {FALSE, TRUE}]""") { rewriterType: SMTEncoding =>
    val domain = enumSet(int(1), int(2), int(3))
    val codomain = enumSet(bool(false), bool(true))
    val fs = funSet(domain, codomain)
    val state = new SymbState(fs, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        val cell = nextState.arena.findCellByNameEx(nextState.ex)
        assert(cell.cellType == FinFunSetT(CellTFrom(SetT1(IntT1)), CellTFrom(SetT1(BoolT1))))
        val dom = nextState.arena.getDom(cell)
        assert(dom.cellType == CellTFrom(SetT1(IntT1)))
        val domElems = nextState.arena.getHas(dom)
        assert(domElems.length == 3)
        val cdm = nextState.arena.getCdm(cell)
        assert(cdm.cellType == CellTFrom(SetT1(BoolT1)))
        val cdmElems = nextState.arena.getHas(cdm)
        assert(cdmElems.length == 2)
      // the contents is tested in the rules below

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""[{1, 2} -> Expand(SUBSET {FALSE, TRUE})]""") { rewriterType: SMTEncoding =>
    val domain = enumSet(int(1), int(2))
    val codomain = expand(powSet(enumSet(bool(false), bool(true))))
    val fs = funSet(domain, codomain)

    val state = new SymbState(fs, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        val cell = nextState.arena.findCellByNameEx(nextState.ex)
        assert(cell.cellType == FinFunSetT(CellTFrom(SetT1(IntT1)), CellTFrom(SetT1(SetT1(BoolT1)))))
        val dom = nextState.arena.getDom(cell)
        assert(dom.cellType == CellTFrom(SetT1(IntT1)))
        val domElems = nextState.arena.getHas(dom)
        assert(domElems.length == 2)
        val cdm = nextState.arena.getCdm(cell)
        assert(cdm.cellType == CellTFrom(SetT1(SetT1(BoolT1))))

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // the existential over a function set should work without expanding the powerset!
  test("""Skolem(\E f \in [{1, 2} -> SUBSET {FALSE, TRUE}]: g' <- f)""") { rewriterType: SMTEncoding =>
    val domain = enumSet(int(1), int(2))
    val codomain = powSet(enumSet(bool(false), bool(true)))
    val pred = assign(prime(name("g", i_to_B)), name("f", i_to_B))

    val existsForm =
      exists(name("f", i_to_B), funSet(domain, codomain), pred)

    val skolemEx = skolem(existsForm)

    val state = new SymbState(skolemEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val gprime = nextState.binding("g'")
    assert(CellTFrom(FunT1(IntT1, SetT1(BoolT1))) == gprime.cellType)
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  // the existential over a function set should work correctly in presence of duplicates
  test("""Skolem(\E f \in [{1, 2 - 1, 2} -> SUBSET {FALSE, TRUE}]: g' <- f)""") { rewriterType: SMTEncoding =>
    val domain = enumSet(int(1), minus(int(2), int(1)), int(2))
//    val domain = enumSet(int(1), int(1), int(2))
    val codomain = powSet(enumSet(bool(false), bool(true)))
    val pred = assign(prime(name("g", i_to_B)), name("f", i_to_B))

    val existsForm = exists(name("f", i_to_B), funSet(domain, codomain), pred)

    val skolemEx = skolem(existsForm)

    val state = new SymbState(skolemEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val gprime = nextState.binding("g'")
    assert(CellTFrom(FunT1(IntT1, SetT1(BoolT1))) == gprime.cellType)
    solverContext.assertGroundExpr(nextState.ex)
    // it should be impossible to return two different values for 1
    val app1 = app(gprime.toBuilder, minus(int(2), int(1)))
    val app2 = app(gprime.toBuilder, minus(int(3), int(2)))
    val app1eqApp2 = eql(app1, app2)
    assertTlaExAndRestore(rewriter, nextState.setRex(app1eqApp2))
  }

  // the existential over a function set should work without expanding the powerset!
  test("""Skolem(\E f \in [{1, 2} -> SUBSET {FALSE}]: f[1] = {TRUE})""") { rewriterType: SMTEncoding =>
    val domain = enumSet(int(1), int(2))
    val codomain = powSet(enumSet(bool(false)))
    val pred = eql(app(name("f", i_to_B), int(1)), enumSet(bool(true)))

    val existsForm = exists(name("f", i_to_B), funSet(domain, codomain), pred)
    val skolemEx = skolem(existsForm)

    val state = new SymbState(skolemEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  // An existential over a function set that returns a function set to a powerset. Does it blow up your mind? :-)
  test("""Skolem(\E f \in [{1, 2} -> [{3} -> SUBSET {FALSE, TRUE}]]: g' <- f)""") { rewriterType: SMTEncoding =>
    val domain1 = enumSet(int(1), int(2))
    val domain2 = enumSet(int(3))
    val codomain2 = powSet(enumSet(bool(false), bool(true)))
    val codomain1 = funSet(domain2, codomain2)
    val funset = funSet(domain1, codomain1)

    val pred = assign(prime(name("g", i_to_i_to_B)), name("f", i_to_i_to_B))

    val existsForm =
      exists(name("f", i_to_i_to_B), funset, pred)

    val skolemEx = skolem(existsForm)

    val state = new SymbState(skolemEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val gprime = nextState.binding("g'")
    assert(CellTFrom(FunT1(IntT1, FunT1(IntT1, SetT1(BoolT1)))) == gprime.cellType)
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  // this should be fixed by implementing #91
  test("""[x \in {1, 2} |-> {x = 1}] \in [{1, 2} -> SUBSET {FALSE, TRUE}]""") { rewriterType: SMTEncoding =>
    val domain = enumSet(int(1), int(2))
    val codomain = powSet(enumSet(bool(false), bool(true)))
    val funset = funSet(domain, codomain)
    val fun = funDef(enumSet(eql(name("x", IntT1), int(1))), name("x", IntT1) -> domain)

    val funInFunSet = in(fun, funset)

    val state = new SymbState(funInFunSet, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""[x \in {1, 2} |-> 3] \in [{1, 2} -> {3, 4}]""") { rewriterType: SMTEncoding =>
    val domain = enumSet(int(1), int(2))
    val codomain = enumSet(int(3), int(4))
    val funset = funSet(domain, codomain)
    val fun = funDef(int(3), name("x", IntT1) -> domain)

    val funInFunSet = in(fun, funset)

    val state = new SymbState(funInFunSet, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  // this should be redundant in the presence of #91
  test("""[x \in {0, 1, 2} \ {0} |-> 3] \in [{1, 2} -> {3, 4}]""") { rewriterType: SMTEncoding =>
    // although 0 is in the function domain at the arena level, it does not belong to the set difference
    def setminus(set: TBuilderInstruction, intVal: BigInt): TBuilderInstruction = {
      filter(name("t", IntT1), set, not(eql(name("t", IntT1), int(intVal))))

    }

    val domain1 = setminus(enumSet(0.to(2).map(i => int(BigInt(i))): _*), 0)
    val domain2 = enumSet(1.to(2).map(i => int(BigInt(i))): _*)

    val codomain = enumSet(int(3), int(4))

    val funset = funSet(domain2, codomain)

    val fun = funDef(int(3), name("x", IntT1) -> domain1)

    val funInFunSet = in(fun, funset)

    val state = new SymbState(funInFunSet, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  // this should be fixed by implementing #91
  test("""[x \in {1, 2} |-> {TRUE}] \in [{1, 2} -> SUBSET {FALSE}]""") { rewriterType: SMTEncoding =>
    val domain = enumSet(int(1), int(2))
    val codomain = powSet(enumSet(bool(false)))
    val funset = funSet(domain, codomain)

    val fun = funDef(enumSet(bool(true)), name("x", IntT1) -> domain)

    val funInFunSet = in(fun, funset)

    val state = new SymbState(funInFunSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  // this should be fixed by implementing #91
  test("""[x \in {1, 2} |-> {TRUE}] \in [{1, 2} -> SUBSET {FALSE, TRUE}]""") { rewriterType: SMTEncoding =>
    val domain = enumSet(int(1), int(2))
    val codomain = powSet(enumSet(bool(false), bool(true)))
    val funset = funSet(domain, codomain)

    val fun = funDef(enumSet(bool(true)), name("x", IntT1) -> domain)

    val funInFunSet = in(fun, funset)

    val state = new SymbState(funInFunSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  // bugfix 27/12/2017
  test("""SE-FUNSET1: [0..(5 - 1) -> {FALSE, TRUE}]""") { rewriterType: SMTEncoding =>
    val domain = dotdot(int(0), minus(int(5), int(1)))
    val codomain = enumSet(bool(false), bool(true))
    val fs = funSet(domain, codomain)

    val state = new SymbState(fs, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        val cell = nextState.arena.findCellByNameEx(nextState.ex)
        assert(cell.cellType == FinFunSetT(CellTFrom(SetT1(IntT1)), CellTFrom(SetT1(BoolT1))))
        val dom = nextState.arena.getDom(cell)
        assert(dom.cellType == CellTFrom(SetT1(IntT1)))
        val domElems = nextState.arena.getHas(dom)
        assert(domElems.length == 5)
        val cdm = nextState.arena.getCdm(cell)
        assert(cdm.cellType == CellTFrom(SetT1(BoolT1)))
        val cdmElems = nextState.arena.getHas(cdm)
        assert(cdmElems.length == 2)
      // the contents is tested in the rules below

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
