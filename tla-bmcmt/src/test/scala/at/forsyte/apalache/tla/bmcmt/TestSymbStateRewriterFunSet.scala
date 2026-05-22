package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterFunSet extends RewriterBase {
  val i_to_B: TlaType1 = FunT1(IntT1, SetT1(BoolT1))
  val i_to_i_to_B: TlaType1 = FunT1(IntT1, FunT1(IntT1, SetT1(BoolT1)))

  test("""[{1, 2, 3} -> {FALSE, TRUE}]""") { rewriterType: SMTEncoding =>
    val domain = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val codomain = tla.enumSet(tla.bool(false), tla.bool(true))
    val fs = tla.funSet(domain, codomain)
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
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.expand(tla.powSet(tla.enumSet(tla.bool(false), tla.bool(true))))
    val fs = tla.funSet(domain, codomain)

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
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.powSet(tla.enumSet(tla.bool(false), tla.bool(true)))
    val pred = tla.assign(tla.prime(tla.name("g", i_to_B)), tla.name("f", i_to_B))

    val existsForm =
      tla.exists(tla.name("f", i_to_B), tla.funSet(domain, codomain), pred)

    val skolemEx = tla.skolem(existsForm)

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
    val domain = tla.enumSet(tla.int(1), tla.minus(tla.int(2), tla.int(1)), tla.int(2))
//    val domain = tla.enumSet(tla.int(1), tla.int(1), tla.int(2))
    val codomain = tla.powSet(tla.enumSet(tla.bool(false), tla.bool(true)))
    val pred = tla.assign(tla.prime(tla.name("g", i_to_B)), tla.name("f", i_to_B))

    val existsForm = tla.exists(tla.name("f", i_to_B), tla.funSet(domain, codomain), pred)

    val skolemEx = tla.skolem(existsForm)

    val state = new SymbState(skolemEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val gprime = nextState.binding("g'")
    assert(CellTFrom(FunT1(IntT1, SetT1(BoolT1))) == gprime.cellType)
    solverContext.assertGroundExpr(nextState.ex)
    // it should be impossible to return two different values for 1
    val app1 = tla.app(cellEx(gprime), tla.minus(tla.int(2), tla.int(1)))
    val app2 = tla.app(cellEx(gprime), tla.minus(tla.int(3), tla.int(2)))
    val app1eqApp2 = tla.eql(app1, app2)
    assertTlaExAndRestore(rewriter, nextState.setRex(app1eqApp2))
  }

  // the existential over a function set should work without expanding the powerset!
  test("""Skolem(\E f \in [{1, 2} -> SUBSET {FALSE}]: f[1] = {TRUE})""") { rewriterType: SMTEncoding =>
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.powSet(tla.enumSet(tla.bool(false)))
    val pred = tla.eql(tla.app(tla.name("f", i_to_B), tla.int(1)), tla.enumSet(tla.bool(true)))

    val existsForm = tla.exists(tla.name("f", i_to_B), tla.funSet(domain, codomain), pred)
    val skolemEx = tla.skolem(existsForm)

    val state = new SymbState(skolemEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  // An existential over a function set that returns a function set to a powerset. Does it blow up your mind? :-)
  test("""Skolem(\E f \in [{1, 2} -> [{3} -> SUBSET {FALSE, TRUE}]]: g' <- f)""") { rewriterType: SMTEncoding =>
    val domain1 = tla.enumSet(tla.int(1), tla.int(2))
    val domain2 = tla.enumSet(tla.int(3))
    val codomain2 = tla.powSet(tla.enumSet(tla.bool(false), tla.bool(true)))
    val codomain1 = tla.funSet(domain2, codomain2)
    val funset = tla.funSet(domain1, codomain1)

    val pred = tla.assign(tla.prime(tla.name("g", i_to_i_to_B)), tla.name("f", i_to_i_to_B))

    val existsForm =
      tla.exists(tla.name("f", i_to_i_to_B), funset, pred)

    val skolemEx = tla.skolem(existsForm)

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
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.powSet(tla.enumSet(tla.bool(false), tla.bool(true)))
    val funset = tla.funSet(domain, codomain)
    val fun = tla.funDef(tla.enumSet(tla.eql(tla.name("x", IntT1), tla.int(1))), tla.name("x", IntT1) -> domain)

    val funInFunSet = tla.in(fun, funset)

    val state = new SymbState(funInFunSet, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""[x \in {1, 2} |-> 3] \in [{1, 2} -> {3, 4}]""") { rewriterType: SMTEncoding =>
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.enumSet(tla.int(3), tla.int(4))
    val funset = tla.funSet(domain, codomain)
    val fun = tla.funDef(tla.int(3), tla.name("x", IntT1) -> domain)

    val funInFunSet = tla.in(fun, funset)

    val state = new SymbState(funInFunSet, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  // this should be redundant in the presence of #91
  test("""[x \in {0, 1, 2} \ {0} |-> 3] \in [{1, 2} -> {3, 4}]""") { rewriterType: SMTEncoding =>
    // although 0 is in the function domain at the arena level, it does not belong to the set difference
    def setminus(set: TBuilderInstruction, intVal: BigInt): TBuilderInstruction = {
      tla.filter(tla.name("t", IntT1), set, tla.not(tla.eql(tla.name("t", IntT1), tla.int(intVal))))

    }

    val domain1 = setminus(tla.enumSet(0.to(2).map(i => tla.int(BigInt(i))): _*), 0)
    val domain2 = tla.enumSet(1.to(2).map(i => tla.int(BigInt(i))): _*)

    val codomain = tla.enumSet(tla.int(3), tla.int(4))

    val funset = tla.funSet(domain2, codomain)

    val fun = tla.funDef(tla.int(3), tla.name("x", IntT1) -> domain1)

    val funInFunSet = tla.in(fun, funset)

    val state = new SymbState(funInFunSet, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  // this should be fixed by implementing #91
  test("""[x \in {1, 2} |-> {TRUE}] \in [{1, 2} -> SUBSET {FALSE}]""") { rewriterType: SMTEncoding =>
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.powSet(tla.enumSet(tla.bool(false)))
    val funset = tla.funSet(domain, codomain)

    val fun = tla.funDef(tla.enumSet(tla.bool(true)), tla.name("x", IntT1) -> domain)

    val funInFunSet = tla.in(fun, funset)

    val state = new SymbState(funInFunSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  // this should be fixed by implementing #91
  test("""[x \in {1, 2} |-> {TRUE}] \in [{1, 2} -> SUBSET {FALSE, TRUE}]""") { rewriterType: SMTEncoding =>
    val domain = tla.enumSet(tla.int(1), tla.int(2))
    val codomain = tla.powSet(tla.enumSet(tla.bool(false), tla.bool(true)))
    val funset = tla.funSet(domain, codomain)

    val fun = tla.funDef(tla.enumSet(tla.bool(true)), tla.name("x", IntT1) -> domain)

    val funInFunSet = tla.in(fun, funset)

    val state = new SymbState(funInFunSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  // bugfix 27/12/2017
  test("""SE-FUNSET1: [0..(5 - 1) -> {FALSE, TRUE}]""") { rewriterType: SMTEncoding =>
    val domain = tla.dotdot(tla.int(0), tla.minus(tla.int(5), tla.int(1)))
    val codomain = tla.enumSet(tla.bool(false), tla.bool(true))
    val fs = tla.funSet(domain, codomain)

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
