package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.smt.{PreproSolverContext, SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.pp.TlaInputError
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser

trait TestSymbStateRewriterSet extends RewriterBase {
  private val parser = DefaultType1Parser
  private val intT: TlaType1 = IntT1
  private val intSetT: TlaType1 = SetT1(IntT1)
  private val int2SetT: TlaType1 = SetT1(intSetT)
  private val int3SetT: TlaType1 = SetT1(int2SetT)
  private val boolT: TlaType1 = BoolT1

  private def intEnum(values: Int*): TBuilderInstruction = tla.enumSet(values.map(i => tla.int(i)): _*)
  private def emptyIntSet: TBuilderInstruction = tla.emptySet(IntT1)
  private def emptyInt2Set: TBuilderInstruction = tla.emptySet(intSetT)
  private def emptyInt3Set: TBuilderInstruction = tla.emptySet(int2SetT)
  private def emptyInt4Set: TBuilderInstruction = tla.emptySet(int3SetT)
  private def unchecked(ex: TlaEx): TBuilderInstruction = tla.unchecked(ex)

  test("""{ x, y, z } ~~> c_set""") { rewriterType: SMTEncoding =>
    val ex = tla.enumSet(tla.name("x", boolT), tla.name("y", boolT), tla.name("z", boolT))
    val binding = Binding("x" -> arena.cellFalse(), "y" -> arena.cellTrue(), "z" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    create(rewriterType).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case set @ NameEx(_) =>
            val falseInSet = tla.selectInSet(cellEx(arena.cellFalse()), unchecked(set))
            solverContext.assertGroundExpr(falseInSet)
            assert(solverContext.sat())
            val notTrueInSet =
              tla.not(tla.selectInSet(cellEx(arena.cellTrue()), unchecked(set)))
            solverContext.assertGroundExpr(notTrueInSet)
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 3, 5} ~~> c_set""") { rewriterType: SMTEncoding =>
    val ex = tla.enumSet(tla.int(1), tla.int(3), tla.int(5))
    val state = new SymbState(ex, arena, Binding())
    create(rewriterType).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(_) =>
            assert(solverContext.sat())
          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{} \in {}""") { rewriterType: SMTEncoding =>
    val ex = tla.in(emptyIntSet, emptyInt2Set)
    val state = new SymbState(ex, arena, Binding())
    val nextState = create(rewriterType).rewriteUntilDone(state)
    assert(nextState.arena.cellFalse().toNameEx == nextState.ex)
  }

  test("""3 \in {1, 3, 5}""") { rewriterType: SMTEncoding =>
    val ex = tla.in(tla.int(3), tla.enumSet(tla.int(1), tla.int(3), tla.int(5)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{3} \in {{1}, {3}, {5}}""") { rewriterType: SMTEncoding =>
    val ex = tla.in(tla.enumSet(tla.int(3)),
        tla.enumSet(tla.enumSet(tla.int(1)), tla.enumSet(tla.int(3)), tla.enumSet(tla.int(5))))

    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in {1, 3, 5}""") { rewriterType: SMTEncoding =>
    val ex = tla.in(tla.int(2), tla.enumSet(tla.int(1), tla.int(3), tla.int(5)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in Int""") { rewriterType: SMTEncoding =>
    val ex = tla.in(tla.int(2), tla.intSet())
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  test("""2 \in Nat""") { rewriterType: SMTEncoding =>
    val ex = tla.in(tla.int(2), tla.natSet())
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  test("""-1 \in Nat""") { rewriterType: SMTEncoding =>
    val ex = tla.in(tla.int(-1), tla.natSet())
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.not(unchecked(nextState.ex))))
  }

  test("""~({} \in {})""") { rewriterType: SMTEncoding =>
    val ex = tla.not(tla.in(emptyIntSet, emptyInt2Set))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.push()
    solverContext.assertGroundExpr(tla.not(unchecked(nextState.ex)))
    assert(!solverContext.sat())
    solverContext.pop()
  }

  test("""FALSE \in {FALSE, TRUE}""") { rewriterType: SMTEncoding =>
    val ex =
      tla.in(tla.bool(false), tla.enumSet(tla.bool(false), tla.bool(true)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx @ NameEx(_) =>
            rewriter.push()
            solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
            assert(!solverContext.sat())
            rewriter.pop()
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""~(FALSE \in {FALSE, TRUE})""") { rewriterType: SMTEncoding =>
    val ex =
      tla.not(tla.in(tla.bool(false), tla.enumSet(tla.bool(false), tla.bool(true))))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteUntilDone(state).ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""c_i \in {TRUE, TRUE}""") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(BoolT1)
    val cell = arena.topCell
    val ex =
      tla.in(cellEx(cell), tla.enumSet(tla.bool(true), tla.bool(true)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx @ NameEx(_) =>
            rewriter.push()
            // cell = \TRUE
            solverContext.assertGroundExpr(tla.eql(cellEx(arena.cellTrue()), cellEx(cell)))
            // and membership holds true
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())
            rewriter.pop()
            // another query
            // cell = \FALSE
            solverContext.assertGroundExpr(tla.eql(cellEx(arena.cellFalse()), cellEx(cell)))
            // and membership holds true
            solverContext.assertGroundExpr(predEx)
            // contradiction
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""1 \in {1}""") { rewriterType: SMTEncoding =>
    // regression: there is a special shortcut rule for singleton sets, which had a bug
    val ex = tla.in(tla.int(1), tla.enumSet(tla.int(1)))

    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        nextState.arena.appendCell(IntT1) // the buggy rule implementation triggered an error here
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
        assert(!solverContext.sat())
        rewriter.pop()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""~(Bool \in {TRUE, TRUE})""") { rewriterType: SMTEncoding =>
    arena = arena.appendCell(BoolT1)
    val cell = arena.topCell
    val ex =
      tla.not(tla.in(cellEx(cell), tla.enumSet(tla.bool(true), tla.bool(true))))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteUntilDone(state).ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // cell = TRUE
        solverContext.assertGroundExpr(tla.eql(cellEx(arena.cellTrue()), cellEx(cell)))
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        // another query
        // cell = \FALSE
        solverContext.assertGroundExpr(tla.eql(cellEx(arena.cellFalse()), cellEx(cell)))
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        // no contradiction here
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{}, {}}} \in {{}, {{}, {{}, {}}}}""") { rewriterType: SMTEncoding =>
    def intSet(): TBuilderInstruction = emptyIntSet

    def int2Set(): TBuilderInstruction = emptyInt2Set

    def int3Set(): TBuilderInstruction = emptyInt3Set

    val left = tla.enumSet(int2Set(), tla.enumSet(intSet(), intSet()))
    val right =
      tla.enumSet(int3Set(), tla.enumSet(int2Set(), tla.enumSet(intSet(), intSet())))
    val ex = tla.in(left, right)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        // another query
        // and membership does not hold
        solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{{}}}} \in {{}, {{}, {{}}}""") { rewriterType: SMTEncoding =>
    def intSet(): TBuilderInstruction = emptyIntSet

    def int2Set(): TBuilderInstruction = emptyInt2Set

    def int3Set(): TBuilderInstruction = emptyInt3Set

    def int4Set(): TBuilderInstruction = emptyInt4Set

    val left = tla.enumSet(int3Set(), tla.enumSet(tla.enumSet(intSet())))
    val right = tla.enumSet(int4Set(), tla.enumSet(int3Set(), tla.enumSet(int2Set())))
    val ex = tla.in(left, right)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // set membership should not hold
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        // its negation holds true
        solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}} = {} ~~> (false)""") { rewriterType: SMTEncoding =>
    def intSet(): TBuilderInstruction = emptyIntSet

    def int2Set(): TBuilderInstruction = emptyInt2Set

    val ex = tla.eql(tla.enumSet(intSet()), int2Set())
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{}}} = {{}, {{{}}} ~~> (false)""") { rewriterType: SMTEncoding =>
    def intSet(): TBuilderInstruction = emptyIntSet

    def int2Set(): TBuilderInstruction = emptyInt2Set

    def int3Set(): TBuilderInstruction = emptyInt3Set

    val left = tla.enumSet(int3Set(), tla.enumSet(int2Set()))
    val right = tla.enumSet(int3Set(), tla.enumSet(tla.enumSet(intSet())))
    val ex = tla.eql(left, right)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{}}} = {{}, {{}} ~~> (true)""") { rewriterType: SMTEncoding =>
    def intSet(): TBuilderInstruction = emptyIntSet

    def int2Set(): TBuilderInstruction = emptyInt2Set

    val left = tla.enumSet(int2Set(), tla.enumSet(intSet()))
    val right = tla.enumSet(int2Set(), tla.enumSet(intSet()))
    val ex = tla.eql(left, right)

    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{} = {1} \ {1} ~~> (true)""") { rewriterType: SMTEncoding =>
    def intSet(): TBuilderInstruction = emptyIntSet

    val setOf1 = tla.enumSet(tla.int(1))

    val dynEmpty =
      tla.filter(tla.name("t", intT), setOf1, tla.bool(false))

    val ex = tla.eql(intSet(), dynEmpty)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // equal
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""~({{}, {{}}} = {{}, {{}}})""") { rewriterType: SMTEncoding =>
    def intSet(): TBuilderInstruction = emptyIntSet

    def int2Set(): TBuilderInstruction = emptyInt2Set

    val left = tla.enumSet(int2Set(), tla.enumSet(intSet()))
    val right = tla.enumSet(int2Set(), tla.enumSet(intSet()))
    val ex = tla.not(tla.eql(left, right))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
  test("""{x \in {1,2,3,4} : x % 2 = 0} ~~> {2, 4}""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(tla.int(1), tla.int(2), tla.int(3), tla.int(4))
    val xMod2 = tla.mod(tla.name("x", intT), tla.int(2))
    val pred = tla.eql(xMod2, tla.int(0))
    val ex = tla.filter(tla.name("x", intT), set, pred)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        rewriter.push()
        assert(solverContext.sat())
      // we check actual membership in another test

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in {x \in {1,2,3,4} : x < 3}""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(tla.int(1), tla.int(2), tla.int(3), tla.int(4))
    val pred = tla.lt(tla.name("x", intT), tla.int(3))
    val filteredSet = tla.filter(tla.name("x", intT), set, pred)
    val inFilteredSet = tla.in(tla.int(2), filteredSet)

    val state = new SymbState(inFilteredSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(unchecked(membershipEx)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{Q \in Expand(SUBSET {1,2,3}) : ~(2 \in Q)}""") { rewriterType: SMTEncoding =>
    val set = intEnum(1, 2, 3)

    val predEx = tla.not(tla.in(tla.int(2), tla.name("Q", intSetT)))
    val expandedPowSet = tla.expand(tla.powSet(set))
    val ex = tla.filter(tla.name("Q", intSetT), expandedPowSet, unchecked(predEx))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val inPred = tla.in(tla.enumSet(tla.int(1), tla.int(3)), unchecked(nextState.ex))
    assertTlaExAndRestore(rewriter, nextState.setRex(inPred))
    val notInPred = tla.not(tla.in(tla.enumSet(tla.int(1), tla.int(2)), unchecked(nextState.ex)))
    assertTlaExAndRestore(rewriter, nextState.setRex(notInPred))
  }

  test("""\E X \in SUBSET {1} IN {} = {x \in X : [y \in X |-> TRUE][x]}""") { rewriterType: SMTEncoding =>
    // regression
    val baseSet = tla.enumSet(tla.int(1))
    val pred =
      tla.app(tla.funDef(tla.bool(true), tla.name("y", intT) -> tla.name("X", intSetT)), tla.name("x", intT))
    val filteredSet = tla.filter(tla.name("x", intT), tla.name("X", intSetT), pred)
    val ex =
      tla.skolem(tla.exists(tla.name("X", intSetT), tla.powSet(baseSet), tla.eql(emptyIntSet, filteredSet)))

    val state = new SymbState(ex, arena, Binding())
    val rewriter = createWithoutCache(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        assert(solverContext.sat())
        rewriter.push()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""\E X \in SUBSET {1, 2}: {} = {x \in X : [y \in {1} |-> TRUE][x]}""") { rewriterType: SMTEncoding =>
    // regression
    val set1 = tla.enumSet(tla.int(1))
    val pred = tla.app(tla.funDef(tla.bool(true), tla.name("y", intT) -> set1), tla.name("x", intT))
    val filteredSet = tla.filter(tla.name("x", intT), tla.name("X", intSetT), pred)
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val ex =
      tla.skolem(tla.exists(tla.name("X", intSetT), tla.powSet(set12), tla.eql(emptyIntSet, filteredSet)))

    val state = new SymbState(ex, arena, Binding())
    val rewriter = createWithoutCache(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        // the new implementation just returns a default value, as in the classical TLA+ interpretation
        assert(solverContext.sat())
        // the result should be true, although some values may be undefined
        solverContext.assertGroundExpr(nextState.ex)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""3 \in {x \in {2, 3} : x % 2 = 0}""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(tla.int(2), tla.int(3))
    val xMod2 = tla.mod(tla.name("x", intT), tla.int(2))
    val pred = tla.eql(xMod2, tla.int(0))
    val filteredSet = tla.filter(tla.name("x", intT), set, pred)
    val inFilteredSet = tla.in(tla.int(3), filteredSet)

    val state = new SymbState(inFilteredSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(unchecked(membershipEx)))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{ x / 3: x \in {1,2,3,4} }""") { rewriterType: SMTEncoding =>
    val set = intEnum(1, 2, 3, 4)
    val mapping = tla.div(tla.name("x", intT), tla.int(3))
    val mappedSet = tla.map(mapping, tla.name("x", intT) -> set)

    val state = new SymbState(mappedSet, arena, Binding())
    val nextState = create(rewriterType).rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        assert(solverContext.sat())
      // membership tests are in the tests below

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""0 \in {x / 3: x \in {1,2,3,4}}""") { rewriterType: SMTEncoding =>
    val set = intEnum(1, 2, 3, 4)
    val mapping = tla.div(tla.name("x", intT), tla.int(3))
    val mappedSet = tla.map(mapping, tla.name("x", intT) -> set)
    val inMappedSet = tla.in(tla.int(0), mappedSet)

    val state = new SymbState(inMappedSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(unchecked(membershipEx)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in {x / 3: x \in {1,2,3,4}}""") { rewriterType: SMTEncoding =>
    val set = intEnum(1, 2, 3, 4)
    val mapping = tla.div(tla.name("x", intT), tla.int(3))
    val mappedSet = tla.map(mapping, tla.name("x", intT) -> set)
    val inMappedSet = tla.in(tla.int(2), mappedSet)

    val state = new SymbState(inMappedSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(unchecked(membershipEx)))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // type inference would reject this
  test("""error: {x: x \in Int}""") { rewriterType: SMTEncoding =>
    val set = tla.intSet()
    val mapSet = tla.map(tla.name("x", intT), tla.name("x", intT) -> set)

    val state = new SymbState(mapSet, arena, Binding())
    val rewriter = create(rewriterType)
    assertThrows[TlaInputError](rewriter.rewriteUntilDone(state))
  }

  test("""<<2, true>> \in {<<x, y>>: x \in {1,2,3}, y \in {FALSE, TRUE}}""") { rewriterType: SMTEncoding =>
    val set123 = intEnum(1, 2, 3)
    val setBool = tla.enumSet(tla.bool(false), tla.bool(true))
    val mapping = tla.tuple(tla.name("x", intT), tla.name("y", boolT))
    val mappedSet = tla.map(mapping, tla.name("x", intT) -> set123, tla.name("y", boolT) -> setBool)
    val inMappedSet = tla.in(tla.tuple(tla.int(2), tla.bool(true)), mappedSet)

    val state = new SymbState(inMappedSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(unchecked(membershipEx)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""<<TRUE>> \in {<<y>>: x \in {1,2} \ {2}, y \in {FALSE, TRUE}}""") { rewriterType: SMTEncoding =>
    // this expression tests regressions in cached expressions
    // we express {1, 2} \ {2} as a filter, as set difference is not in KerA+
    val set12minus2 =
      tla.filter(tla.name("z", intT), tla.enumSet(tla.int(1), tla.int(2)), tla.eql(tla.name("z", intT), tla.int(1)))
    val setBool = tla.enumSet(tla.bool(false), tla.bool(true))
    val mapping = tla.tuple(tla.name("y", boolT))
    val mappedSet =
      tla.map(
          mapping,
          tla.name("x", intT) -> set12minus2,
          tla.name("y", boolT) -> setBool,
      )
    val inMappedSet = tla.in(tla.tuple(tla.bool(true)), mappedSet)

    val state = new SymbState(inMappedSet, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(unchecked(membershipEx)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // Regression for the issue 365: https://github.com/apalache-mc/apalache/issues/365
  test("""MAP: \E S \in SUBSET { [a: "a", b: 1], [a: "a", b: 2] }:  "a" \in { r.a: r \in S }""") {
    rewriterType: SMTEncoding =>
      // this test reveals a deep bug in the encoding: SUBSET {[a: 1, b: 1], [a: 1, b: 2]} produces a powerset,
      // whose elements are sets that refer to the same cells,
      // namely the cells for the records [a: 1, b: 1] and [a: 1, b: 2].
      // If one record is included in a subset, but the other is not, then the map rule produced a contradicting constraint
      // for the element "a": it must be in the resulting set, and at the same time it must not be in the resulting set.
      val recT = parser("[a: Str, b: Int]")
      val recSetT = parser("Set([a: Str, b: Int])")
      val rec1 = tla.rec("a" -> tla.str("a"), "b" -> tla.int(1))
      val rec2 = tla.rec("a" -> tla.str("a"), "b" -> tla.int(2))
      val base = tla.enumSet(rec1, rec2)
      val powerset = tla.powSet(base)
      val mapped =
        tla.map(tla.app(tla.name("r", recT), tla.str("a")), tla.name("r", recT) -> tla.name("S", recSetT))
      val mem = tla.in(tla.str("a"), mapped)
      val existsForm = tla.skolem(tla.exists(tla.name("S", recSetT), powerset, mem))

      // the following test goes through without a need for a fix
      val rewriter = create(rewriterType)
      val state = new SymbState(existsForm, arena, Binding())
      assumeTlaEx(rewriter, state)

      // the following test captures the core of the functional test in `test/tla/Fix365_ExistsSubset3.tla`,
      // which needed a fix
      // \E S \in SUBSET { [a: "a", b: 1], [a: "a", b: 2] }:  "a" \in { r.a: r \in S } /\ \A x \in S: x.b = 2
      val forallForm =
        tla.forall(tla.name("x", recT), tla.name("S", recSetT),
            tla.eql(tla.app(tla.name("x", recT), tla.str("b")), tla.int(2)))
      val existsForm2 =
        tla.skolem(tla.exists(tla.name("S", recSetT), powerset, tla.and(mem, forallForm)))

      // reset the solver and arena
      solverContext = new PreproSolverContext(new Z3SolverContext(SolverConfig.default.copy(debug = true,
                  smtEncoding = rewriterType)))
      arena = PureArenaAdapter.create(solverContext)
      val rewriter2 = create(rewriterType)
      val state2 = new SymbState(existsForm2, arena, Binding())
      assumeTlaEx(rewriter2, state2)
  }

  test("""{1, 3} \cup {3, 4} = {1, 3, 4}""") { rewriterType: SMTEncoding =>
    val left = tla.enumSet(tla.int(1), tla.int(3))
    val right = tla.enumSet(tla.int(3), tla.int(4))
    val expected = tla.enumSet(tla.int(1), tla.int(3), tla.int(4))
    val cupSet = tla.cup(left, right)
    val eqExpected = tla.eql(cupSet, expected)

    val state = new SymbState(eqExpected, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        assert(solverContext.sat())
        // check equality
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 2} \subseteq {1, 2, 3} ~~> (true)""") { rewriterType: SMTEncoding =>
    rewriterType match {
      case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
        () // \subseteq is rewritten in Keramelizer, and SetInclusionRule was removed
      case SMTEncoding.Arrays =>
        val left = tla.enumSet(tla.int(1), tla.int(2))
        val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
        val ex = tla.subseteq(left, right)
        val state = new SymbState(ex, arena, Binding())
        val rewriter = create(rewriterType)
        val nextState = rewriter.rewriteUntilDone(state)
        nextState.ex match {
          case predEx @ NameEx(_) =>
            rewriter.push()
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())
            rewriter.pop()
            rewriter.push()
            solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
            assertUnsatOrExplain()

          case _ =>
            fail("Unexpected rewriting result")
        }
    }
  }

  test("""{1, 2, 3} \subseteq {1, 2, 3} ~~> (true)""") { rewriterType: SMTEncoding =>
    rewriterType match {
      case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
        () // \subseteq is rewritten in Keramelizer, and SetInclusionRule was removed
      case SMTEncoding.Arrays =>
        val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
        val ex = tla.subseteq(right, right)
        val state = new SymbState(ex, arena, Binding())
        val rewriter = create(rewriterType)
        val nextState = rewriter.rewriteUntilDone(state)
        nextState.ex match {
          case predEx @ NameEx(_) =>
            rewriter.push()
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())
            rewriter.pop()
            rewriter.push()
            solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
            assertUnsatOrExplain()

          case _ =>
            fail("Unexpected rewriting result")
        }
    }
  }

  test("""{} \subseteq {1, 2, 3} ~~> (true)""") { rewriterType: SMTEncoding =>
    rewriterType match {
      case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
        () // \subseteq is rewritten in Keramelizer, and SetInclusionRule was removed
      case SMTEncoding.Arrays =>
        val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
        // an empty set requires a type annotation
        val ex = tla.subseteq(emptyIntSet, right)
        val state = new SymbState(ex, arena, Binding())
        val rewriter = create(rewriterType)
        val nextState = rewriter.rewriteUntilDone(state)
        nextState.ex match {
          case predEx @ NameEx(_) =>
            rewriter.push()
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())
            rewriter.pop()
            rewriter.push()
            solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
            assertUnsatOrExplain()

          case _ =>
            fail("Unexpected rewriting result")
        }
    }
  }

  test("""{1, 4} \subseteq {1, 2, 3} ~~> (false)""") { rewriterType: SMTEncoding =>
    rewriterType match {
      case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
        () // \subseteq is rewritten in Keramelizer, and SetInclusionRule was removed
      case SMTEncoding.Arrays =>
        val left = tla.enumSet(tla.int(1), tla.int(4))
        val right = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
        val ex = tla.subseteq(left, right)
        val state = new SymbState(ex, arena, Binding())
        val rewriter = create(rewriterType)
        val nextState = rewriter.rewriteUntilDone(state)
        nextState.ex match {
          case predEx @ NameEx(_) =>
            rewriter.push()
            solverContext.assertGroundExpr(predEx)
            assertUnsatOrExplain()
            rewriter.pop()
            rewriter.push()
            solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
            assert(solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }
    }
  }

  test("""{[x \in {1, 2} |-> TRUE ]} \subseteq {[x \in {1, 2} |-> TRUE ]} ~~> (true)""") { rewriterType: SMTEncoding =>
    rewriterType match {
      case SMTEncoding.OOPSLA19 | SMTEncoding.FunArrays =>
        () // \subseteq is rewritten in Keramelizer, and SetInclusionRule was removed
      case SMTEncoding.Arrays =>
        val dom = tla.enumSet(tla.int(1), tla.int(2))
        val mapping = tla.bool(true)
        val fun = tla.funDef(mapping, tla.name("x", IntT1) -> dom)
        val set = tla.enumSet(fun)

        val ex = tla.subseteq(set, set)
        val state = new SymbState(ex, arena, Binding())
        val rewriter = create(rewriterType)
        val nextState = rewriter.rewriteUntilDone(state)
        nextState.ex match {
          case predEx @ NameEx(_) =>
            rewriter.push()
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())
            rewriter.pop()
            rewriter.push()
            solverContext.assertGroundExpr(tla.not(unchecked(predEx)))
            assertUnsatOrExplain()

          case _ =>
            fail("Unexpected rewriting result")
        }
    }
  }

  test("""UNION {{1, 2}, {2,3}} = {1, 2, 3}""") { rewriterType: SMTEncoding =>
    val setOf12 = tla.enumSet(tla.int(1), tla.int(2))
    val setOf23 = tla.enumSet(tla.int(3), tla.int(2))
    val setOf123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    // This may seem weird, but since we don't know the type of {},
    // it should be equal to the empty set of ints.
    val eq = tla.eql(tla.union(tla.enumSet(setOf12, setOf23)), setOf123)
    val rewriter = create(rewriterType)
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

}
