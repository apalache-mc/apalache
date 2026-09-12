package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.config.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterFunSet extends RewriterBase {
  val i_to_B: TlaType1 = FunT1(IntT1, SetT1(BoolT1))
  val i_to_i_to_B: TlaType1 = FunT1(IntT1, FunT1(IntT1, SetT1(BoolT1)))

  private def assertForBothGuardValues(rewriter: SymbStateRewriter, state: SymbState, guard: ArenaCell): Unit = {
    rewriter.push()
    val nextState = rewriter.rewriteUntilDone(state)
    for (value <- Seq(false, true)) {
      rewriter.push()
      rewriter.solverContext.assertGroundExpr(tla.eql(guard.toBuilder, tla.bool(value)))
      assertTlaExAndRestore(rewriter, nextState)
      rewriter.pop()
    }
    rewriter.pop()
  }

  // Keep all four operands symbolic so constructor normalization cannot hide the lazy-equality bug.
  for (sameDomain <- Seq(false, true); sameCodomain <- Seq(false, true)) {
    test(s"function-set equality (#3477): symbolic operands, sameDomain=$sameDomain, sameCodomain=$sameCodomain") {
      rewriterType: SMTEncoding =>
        val rewriter = create(rewriterType)
        var state = new SymbState(tla.bool(true), arena, Binding())
        val guards = (0 until 4).map { _ =>
          state = state.updateArena(_.appendCell(BoolT1))
          state.arena.topCell
        }

        def operand(index: Int, value: Int): TBuilderInstruction =
          tla.ite(guards(index).toBuilder, tla.enumSet(tla.int(value)), tla.emptySet(IntT1))

        state = rewriter.rewriteUntilDone(state.setRex(tla.funSet(operand(0, 1), operand(1, 3))))
        val left = state.asCell
        state = rewriter.rewriteUntilDone(state.setRex(tla.funSet(operand(2, if (sameDomain) 1 else 2),
                    operand(3, if (sameCodomain) 3 else 4))))
        val right = state.asCell
        assert(left.cellType.isInstanceOf[FinFunSetT])
        assert(right.cellType.isInstanceOf[FinFunSetT])

        // Repeat after pop, reversing the operands, to exercise equality-cache scoping and symmetry.
        for ((a, b) <- Seq((left, right), (right, left))) {
          rewriter.push()
          val eqState = rewriter.rewriteUntilDone(state.setRex(tla.eql(a.toBuilder, b.toBuilder)))
          for (mask <- 0 until 16) {
            val present = guards.indices.map(i => (mask & (1 << i)) != 0)
            val d1 = present(0)
            val c1 = present(1)
            val d2 = present(2)
            val c2 = present(3)
            val expected =
              (!d1 && !d2) || (d1 && d2 && !c1 && !c2) ||
                (d1 && d2 && c1 && c2 && sameDomain && sameCodomain)
            rewriter.push()
            guards.zip(present).foreach { case (guard, value) =>
              rewriter.solverContext.assertGroundExpr(tla.eql(guard.toBuilder, tla.bool(value)))
            }
            withClue(s"membership mask=$mask: ") {
              // Check consistency as well as validity: an inconsistent encoding must not pass vacuously.
              assertTlaExAndRestore(rewriter, eqState.setRex(tla.eql(tla.unchecked(eqState.ex), tla.bool(expected))))
            }
            rewriter.pop()
          }
          rewriter.pop()
        }
    }
  }

  for (filterDomain <- Seq(false, true)) {
    test(s"function-set equality (#3477): filtered operand, filterDomain=$filterDomain") { rewriterType: SMTEncoding =>
      val rewriter = create(rewriterType)
      val withGuard = arena.appendCell(BoolT1)
      val guard = withGuard.topCell
      val filtered = tla.filter(tla.name("x", IntT1), tla.enumSet(tla.int(1), tla.int(2)),
          tla.and(guard.toBuilder, tla.eql(tla.name("x", IntT1), tla.int(1))))
      var state = rewriter.rewriteUntilDone(new SymbState(filtered, withGuard, Binding()))
      val set = state.asCell
      assert(state.arena.getHas(set).nonEmpty)

      def funSet(value: Int): TBuilderInstruction =
        if (filterDomain) tla.funSet(set.toBuilder, tla.enumSet(tla.int(value)))
        else tla.funSet(tla.enumSet(tla.int(value)), set.toBuilder)

      state = rewriter.rewriteUntilDone(state.setRex(funSet(3)))
      val left = state.asCell
      state = rewriter.rewriteUntilDone(state.setRex(funSet(4)))
      val right = state.asCell
      assert(left.cellType.isInstanceOf[FinFunSetT])
      assert(right.cellType.isInstanceOf[FinFunSetT])
      val eq = tla.eql(left.toBuilder, right.toBuilder)
      assertForBothGuardValues(rewriter, state.setRex(tla.eql(eq, tla.not(guard.toBuilder))), guard)
    }
  }

  for (sameOuterDomain <- Seq(false, true)) {
    test(s"function-set equality (#3477): nested codomains, sameOuterDomain=$sameOuterDomain") {
      rewriterType: SMTEncoding =>
        val rewriter = create(rewriterType)
        val withGuard = arena.appendCell(BoolT1)
        val guard = withGuard.topCell
        val codomain = tla.ite(guard.toBuilder, tla.emptySet(IntT1), tla.enumSet(tla.int(3)))
        val leftEx = tla.funSet(tla.enumSet(tla.int(0)), tla.funSet(tla.enumSet(tla.int(1)), codomain))
        val rightEx = tla
          .funSet(tla.enumSet(tla.int(if (sameOuterDomain) 0 else 10)), tla.funSet(tla.enumSet(tla.int(2)), codomain))
        var state = rewriter.rewriteUntilDone(new SymbState(leftEx, withGuard, Binding()))
        val left = state.asCell
        state = rewriter.rewriteUntilDone(state.setRex(rightEx))
        val right = state.asCell
        assert(state.arena.getCdm(left).cellType.isInstanceOf[FinFunSetT])
        assert(state.arena.getCdm(right).cellType.isInstanceOf[FinFunSetT])
        val eq = tla.eql(left.toBuilder, right.toBuilder)
        assertForBothGuardValues(rewriter, state.setRex(tla.eql(eq, guard.toBuilder)), guard)
    }
  }

  test("function-set equality (#3477): mixed conditional empty-function singleton and lazy set") {
    rewriterType: SMTEncoding =>
      val rewriter = create(rewriterType)
      var state = new SymbState(tla.bool(true), arena, Binding())
      val guards = (0 until 3).map { _ =>
        state = state.updateArena(_.appendCell(BoolT1))
        state.arena.topCell
      }

      def operand(index: Int, value: Int): TBuilderInstruction =
        tla.ite(guards(index).toBuilder, tla.emptySet(IntT1), tla.enumSet(tla.int(value)))

      state = rewriter.rewriteUntilDone(state.setRex(tla.funSet(operand(0, 1), tla.emptySet(IntT1))))
      val ordinary = state.asCell
      state = rewriter.rewriteUntilDone(state.setRex(tla.funSet(operand(1, 2), operand(2, 3))))
      val lazySet = state.asCell
      assert(ordinary.cellType == CellTFrom(SetT1(FunT1(IntT1, IntT1))))
      assert(lazySet.cellType.isInstanceOf[FinFunSetT])
      for ((left, right) <- Seq((ordinary, lazySet), (lazySet, ordinary))) {
        rewriter.push()
        val eqState = rewriter.rewriteUntilDone(state.setRex(tla.eql(left.toBuilder, right.toBuilder)))
        for (mask <- 0 until 8) {
          val empty = guards.indices.map(i => (mask & (1 << i)) != 0)
          val expected = (empty(0) && empty(1)) || (!empty(0) && !empty(1) && empty(2))
          rewriter.push()
          guards.zip(empty).foreach { case (guard, value) =>
            rewriter.solverContext.assertGroundExpr(tla.eql(guard.toBuilder, tla.bool(value)))
          }
          assertTlaExAndRestore(rewriter, eqState.setRex(tla.eql(tla.unchecked(eqState.ex), tla.bool(expected))))
          rewriter.pop()
        }
        rewriter.pop()
      }
  }

  test("function-set equality (#3477): nested mixed representations") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    val withGuard = arena.appendCell(BoolT1)
    val guard = withGuard.topCell
    val domain = tla.ite(guard.toBuilder, tla.emptySet(IntT1), tla.enumSet(tla.int(1)))
    val left = tla.funSet(tla.enumSet(tla.int(0)), tla.funSet(domain, tla.emptySet(IntT1)))
    val right = tla.funSet(tla.enumSet(tla.int(0)), tla.funSet(domain, tla.enumSet(tla.int(2))))
    val assertions = tla.and(
        tla.eql(tla.eql(left, right), guard.toBuilder),
        tla.eql(tla.eql(tla.enumSet(left), tla.enumSet(right)), guard.toBuilder),
    )
    val state = new SymbState(assertions, withGuard, Binding())
    assertForBothGuardValues(rewriter, state, guard)
  }

  test("function-set equality (#3477): reject general mixed enumerated function sets") { rewriterType: SMTEncoding =>
    val domain = tla.enumSet(tla.int(1))
    val fun = tla.funDef(tla.int(2), tla.name("x", IntT1) -> domain)
    val equality = tla.eql(tla.funSet(domain, tla.enumSet(tla.int(2))), tla.enumSet(fun))
    val rewriter = create(rewriterType)
    val error = intercept[RewriterException] {
      rewriter.rewriteUntilDone(new SymbState(equality, arena, Binding()))
    }
    assert(error.getMessage.contains("enumerated set of nonempty-domain functions"))
  }

  test("function-set equality (#3477): reject unsupported lazy operand equality") { rewriterType: SMTEncoding =>
    val domain = tla.enumSet(tla.int(0))
    val left = tla.funSet(domain, tla.powSet(tla.enumSet(tla.int(1))))
    val right = tla.funSet(domain, tla.powSet(tla.enumSet(tla.int(2))))
    val rewriter = create(rewriterType)
    // Unexpanded powersets have no ordinary membership edges. Treating them as enumerated sets would equate them.
    intercept[CheckerException] {
      rewriter.rewriteUntilDone(new SymbState(tla.eql(left, right), arena, Binding()))
    }
  }

  test("function-set equality (#3477): literal degenerate sets") { rewriterType: SMTEncoding =>
    val empty = tla.emptySet(IntT1)
    val one = tla.enumSet(tla.int(1))
    val two = tla.enumSet(tla.int(2))
    val assertions = tla.and(
        tla.eql(tla.funSet(empty, one), tla.funSet(empty, two)),
        tla.eql(tla.funSet(one, empty), tla.funSet(two, empty)),
        tla.not(tla.eql(tla.funSet(empty, empty), tla.funSet(one, empty))),
        tla.not(tla.eql(tla.funSet(one, one), tla.funSet(one, two))),
    )
    assertTlaExAndRestore(create(rewriterType), new SymbState(assertions, arena, Binding()))
  }

  test("[{} -> {}] is a singleton containing the empty function") { rewriterType: SMTEncoding =>
    val funSet = tla.funSet(tla.emptySet(IntT1), tla.emptySet(IntT1))
    val state = new SymbState(funSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val setCell = nextState.asCell

    assert(setCell.cellType == CellTFrom(SetT1(FunT1(IntT1, IntT1))))
    val Seq(FixedElemPtr(emptyFun)) = nextState.arena.getHasPtr(setCell)
    assert(nextState.arena.getHas(nextState.arena.getDom(emptyFun)).isEmpty)
    assert(nextState.arena.getHas(nextState.arena.getCdm(emptyFun)).isEmpty)
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.selectInSet(emptyFun.toBuilder, setCell.toBuilder)))
  }

  test("[{1} -> {}] is empty") { rewriterType: SMTEncoding =>
    val funSet = tla.funSet(tla.enumSet(tla.int(1)), tla.emptySet(IntT1))
    val state = new SymbState(funSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val setCell = nextState.asCell

    assert(setCell.cellType == CellTFrom(SetT1(FunT1(IntT1, IntT1))))
    assert(nextState.arena.getHasPtr(setCell).isEmpty)
  }

  test("[S -> {}] conditionally contains the empty function when S is symbolically empty") {
    rewriterType: SMTEncoding =>
      val arenaWithGuard = arena.appendCell(BoolT1)
      val guard = arenaWithGuard.topCell
      val empty = tla.emptySet(IntT1)
      val singleton = tla.enumSet(tla.int(1))
      val domain = tla.ite(guard.toBuilder, empty, singleton)
      val funSet = tla.funSet(domain, empty)
      val state = new SymbState(funSet, arenaWithGuard, Binding())
      val rewriter = create(rewriterType)
      val nextState = rewriter.rewriteUntilDone(state)
      val setCell = nextState.asCell

      assert(setCell.cellType == CellTFrom(SetT1(FunT1(IntT1, IntT1))))
      val Seq(ptr) = nextState.arena.getHasPtr(setCell)
      val emptyFun = ptr.elem
      val emptyFunInSet = tla.selectInSet(emptyFun.toBuilder, setCell.toBuilder)

      rewriter.push()
      rewriter.solverContext.assertGroundExpr(guard.toBuilder)
      rewriter.solverContext.assertGroundExpr(emptyFunInSet)
      assert(rewriter.solverContext.sat())
      rewriter.pop()

      rewriter.push()
      rewriter.solverContext.assertGroundExpr(tla.not(guard.toBuilder))
      rewriter.solverContext.assertGroundExpr(emptyFunInSet)
      assertUnsatOrExplain()
      rewriter.pop()
  }

  test("separately constructed [{} -> {}] values are equal") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    val funSet1 = tla.funSet(tla.emptySet(IntT1), tla.emptySet(IntT1))
    val state1 = rewriter.rewriteUntilDone(new SymbState(funSet1, arena, Binding()))
    val funSet2 = tla.funSet(tla.emptySet(IntT1), tla.emptySet(IntT1))
    val state2 = rewriter.rewriteUntilDone(state1.setRex(funSet2))
    val equality = tla.eql(state1.asCell.toBuilder, state2.asCell.toBuilder)

    assertTlaExAndRestore(rewriter, state2.setRex(equality))
  }

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
    val app1 = tla.app(gprime.toBuilder, tla.minus(tla.int(2), tla.int(1)))
    val app2 = tla.app(gprime.toBuilder, tla.minus(tla.int(3), tla.int(2)))
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
