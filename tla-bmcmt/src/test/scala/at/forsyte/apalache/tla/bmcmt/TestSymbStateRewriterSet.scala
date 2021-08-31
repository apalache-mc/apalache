package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import at.forsyte.apalache.tla.bmcmt.smt.{PreproSolverContext, SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.types.BuilderTypeInfer._
import at.forsyte.apalache.tla.pp.TlaInputError
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterSet extends RewriterBase {
  private val parser = DefaultType1Parser
  private val intT = parser("Int")
  private val intSetT = parser("Set(Int)")
  private val intSet2T = parser("Set(Set(Int))")
  private val intSet3T = parser("Set(Set(Set(Int)))")
  private val intSet4T = parser("Set(Set(Set(Set(Int))))")
  private val boolT = parser("Bool")
  private val boolSetT = parser("Set(Bool)")

  private val emptyIntSet = enumSet() as intSetT
  private val emptyInt2Set = enumSet() as intSet2T
  private val emptyInt3Set = enumSet() as intSet3T
  private val emptyInt4Set = enumSet() as intSet4T

  test("""{ x, y, z } ~~> c_set""") {
    val ex = enumSet(name("x") as intT, name("y") as intT, name("z") as intT)
    val binding = Binding("x" -> arena.cellFalse(), "y" -> arena.cellTrue(), "z" -> arena.cellFalse())
    val state = new SymbState(ex.inferType(), arena, binding)
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case set @ NameEx(_) =>
            val falseInSet = in(arena.cellFalse().toNameEx as boolT, set as boolSetT).inferType()
            solverContext.assertGroundExpr(falseInSet)
            assert(solverContext.sat())
            val notTrueInSet = not(in(arena.cellTrue().toNameEx as boolT, set as boolSetT)).inferType()
            solverContext
              .assertGroundExpr(notTrueInSet)
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 3, 5} ~~> c_set""") {
    val ex = enumSet(int(1), int(3), int(5))
    val state = new SymbState(ex.inferType(), arena, Binding())
    create().rewriteOnce(state) match {
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

  test("""{} \in {}""") {
    val ex = in(enumSet() as intSetT, enumSet() as intSet2T)
    val state = new SymbState(ex.inferType(), arena, Binding())
    val nextState = create().rewriteUntilDone(state)
    assert(nextState.arena.cellFalse().toNameEx == nextState.ex)
  }

  test("""3 \in {1, 3, 5}""") {
    val ex = in(int(3), enumSet(int(1), int(3), int(5)))
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{3} \in {{1}, {3}, {5}}""") {
    val ex = in(enumSet(int(3)), enumSet(enumSet(int(1)), enumSet(int(3)), enumSet(int(5))))

    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in {1, 3, 5}""") {
    val ex = in(int(2), enumSet(int(1), int(3), int(5)))
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in Int""") {
    val ex = in(int(2), intSet())
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  test("""2 \in Nat""") {
    val ex = in(int(2), natSet())
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
  }

  test("""-1 \in Nat""") {
    val ex = in(int(-1), natSet())
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState.setRex(not(nextState.ex as boolT).inferType()))
  }

  test("""~({} \in {})""") {
    val ex = not(in(enumSet() as intSetT, enumSet() as intSet2T))
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.push()
    solverContext.assertGroundExpr(not(nextState.ex as boolT).inferType())
    assert(!solverContext.sat())
    solverContext.pop()
  }

  test("""FALSE \in {FALSE, TRUE}""") {
    val ex = in(bool(false), enumSet(bool(false), bool(true)))
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx @ NameEx(_) =>
            rewriter.push()
            solverContext.assertGroundExpr(not(predEx as boolT).inferType())
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

  test("""~(FALSE \in {FALSE, TRUE})""") {
    val ex = not(in(bool(false), enumSet(bool(false), bool(true))))
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    rewriter.rewriteUntilDone(state).ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""c_i \in {TRUE, TRUE}""") {
    arena = arena.appendCell(BoolT())
    val cell = arena.topCell
    val ex = in(cell.toNameEx as boolT, enumSet(bool(true), bool(true)))
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case predEx @ NameEx(name) =>
            rewriter.push()
            // cell = TRUE
            solverContext.assertGroundExpr(eql(arena.cellTrue().toNameEx as boolT, cell.toNameEx as boolT).inferType())
            // and membership holds true
            solverContext.assertGroundExpr(predEx)
            assert(solverContext.sat())
            rewriter.pop()
            // another query
            // cell = FALSE
            solverContext.assertGroundExpr(eql(arena.cellFalse().toNameEx as boolT, cell.toNameEx as boolT).inferType())
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

  test("""1 \in {1}""") {
    // regression: there is a special shortcut rule for singleton sets, which had a bug
    val ex = in(int(1), enumSet(int(1)))

    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        nextState.arena.appendCell(IntT()) // the buggy rule implementation triggered an error here
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assert(!solverContext.sat())
        rewriter.pop()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""~(Bool \in {TRUE, TRUE})""") {
    arena = arena.appendCell(BoolT())
    val cell = arena.topCell
    val ex = not(in(cell.toNameEx as boolT, enumSet(bool(true), bool(true))))
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    rewriter.rewriteUntilDone(state).ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        // cell = TRUE
        solverContext.assertGroundExpr(eql(arena.cellTrue().toNameEx as boolT, cell.toNameEx as boolT).inferType())
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        // another query
        // cell = \FALSE
        solverContext.assertGroundExpr(eql(arena.cellFalse().toNameEx as boolT, cell.toNameEx as boolT).inferType())
        // and membership holds true
        solverContext.assertGroundExpr(predEx)
        // no contradiction here
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{}, {}}} \in {{}, {{}, {{}, {}}}}""") {
    val left = enumSet(emptyInt2Set, enumSet(emptyIntSet, emptyIntSet))
    val right = enumSet(emptyInt3Set, enumSet(emptyInt2Set, enumSet(emptyIntSet, emptyIntSet)))
    val ex = in(left, right)
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
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
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{{}}}} \in {{}, {{}, {{}}}""") {
    val left = enumSet(emptyInt3Set, enumSet(enumSet(emptyIntSet)))
    val right = enumSet(emptyInt4Set, enumSet(emptyInt3Set, enumSet(emptyInt2Set)))
    val ex = in(left, right)
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        // set membership should not hold
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())
        rewriter.pop()
        // its negation holds true
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}} = {} ~~> (false)""") {
    val ex = eql(enumSet(emptyIntSet), emptyInt2Set).inferType()
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
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

  test("""{{}, {{}}} = {{}, {{{}}} ~~> (false)""") {
    val left = enumSet(emptyInt3Set, enumSet(emptyInt2Set))
    val right = enumSet(emptyInt3Set, enumSet(enumSet(emptyIntSet)))
    val ex = eql(left, right)
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        // not equal
        solverContext.assertGroundExpr(predEx)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{{}, {{}}} = {{}, {{}} ~~> (true)""") {
    val left = enumSet(emptyInt2Set, enumSet(emptyIntSet))
    val right = enumSet(emptyInt2Set, enumSet(emptyIntSet))
    val ex = eql(left, right)
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
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

  test("""{} = {1} \ {1} ~~> (true)""") {
    val setOf1 = enumSet(int(1))

    val t = name("t") as intT
    val dynEmpty = filter(t, setOf1, bool(false))
    val ex = eql(emptyIntSet, dynEmpty)

    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        // equal
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""~({{}, {{}}} = {{}, {{}}})""") {
    val left = enumSet(emptyInt2Set, enumSet(emptyIntSet))
    val right = enumSet(emptyInt2Set, enumSet(emptyIntSet))
    val ex = not(eql(left, right))

    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
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
  test("""{x \in {1,2,3,4} : x % 2 = 0} ~~> {2, 4}""") {
    val set = enumSet(int(1), int(2), int(3), int(4))
    val x = name("x") as intT
    val xMod2 = mod(x, int(2))
    val pred = eql(xMod2, int(0))
    val ex = filter(x, set, pred)
    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case newSet @ NameEx(name) =>
        rewriter.push()
        assert(solverContext.sat())
      // we check actual membership in another test

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in {x \in {1,2,3,4} : x < 3}""") {
    val x = name("x") as intT
    val set = enumSet(int(1), int(2), int(3), int(4))
    val pred = lt(x, int(3))
    val filteredSet = filter(x, set, pred)
    val inFilteredSet = in(int(2), filteredSet)

    val state = new SymbState(inFilteredSet.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx as boolT).inferType())
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{Q \in Expand(SUBSET {1,2,3}) : ~(2 \in Q)}""") {
    val set = enumSet(1.to(3).map(int): _*)

    val Q = name("Q") as intSetT
    val predEx = not(in(int(2), Q))
    val expandedPowSet = apalacheExpand(powSet(set))
    val ex = filter(Q, expandedPowSet, predEx).inferType()
    val exType = ex.typeTag.asTlaType1()

    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val inPred = in(enumSet(int(1), int(3)), nextState.ex as exType)
    assertTlaExAndRestore(rewriter, nextState.setRex(inPred.inferType()))
    val notInPred = not(in(enumSet(int(1), int(2)), nextState.ex as exType))
    assertTlaExAndRestore(rewriter, nextState.setRex(notInPred.inferType()))
  }

  test("""\E X \in SUBSET {1} IN {} = {x \in X : [y \in X |-> TRUE][x]}""") {
    // regression
    val baseSet = enumSet(int(1))
    val X = name("X") as intSetT
    val x = name("x") as intT
    val y = name("y") as intT
    val pred = appFun(funDef(bool(true), y, X), x)
    val filteredSet = filter(x, X, pred)
    val ex = apalacheSkolem(exists(X, powSet(baseSet), eql(emptyIntSet, filteredSet)))

    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = new SymbStateRewriterImpl(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        assert(solverContext.sat())
        rewriter.push()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""\E X \in SUBSET {1, 2}: {} = {x \in X : [y \in {1} |-> TRUE][x]}""") {
    // regression
    val set1 = enumSet(int(1))
    val x = name("x") as intT
    val y = name("y") as intT
    val X = name("X") as intSetT
    val pred = appFun(funDef(bool(true), y, set1), x)
    val filteredSet = filter(x, X, pred)
    val set12 = enumSet(int(1), int(2))
    val ex = apalacheSkolem(exists(X, powSet(set12), eql(emptyIntSet, filteredSet)))

    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = new SymbStateRewriterImpl(solverContext)
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

  test("""3 \in {x \in {2, 3} : x % 2 = 0}""") {
    val set = enumSet(int(2), int(3))
    val x = name("x") as intT
    val xMod2 = mod(x, int(2))
    val pred = eql(xMod2, int(0))
    val filteredSet = filter(x, set, pred)
    val inFilteredSet = in(int(3), filteredSet)

    val state = new SymbState(inFilteredSet.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx as boolT).inferType())
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{ x / 3: x \in {1,2,3,4} }""") {
    val set = enumSet(1 to 4 map int: _*)
    val x = name("x") as intT
    val mapping = div(x, int(3))
    val mappedSet = map(mapping, x, set)

    val state = new SymbState(mappedSet.inferType(), arena, Binding())
    val nextState = create().rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        assert(solverContext.sat())
      // membership tests are in the tests below

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""0 \in {x / 3: x \in {1,2,3,4}}""") {
    val set = enumSet(1 to 4 map int: _*)
    val x = name("x") as intT
    val mapping = div(x, int(3))
    val mappedSet = map(mapping, x, set)
    val inMappedSet = in(int(0), mappedSet)

    val state = new SymbState(inMappedSet.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx as boolT).inferType())
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""2 \in {x / 3: x \in {1,2,3,4}}""") {
    val set = enumSet(1 to 4 map int: _*)
    val x = name("x") as intT
    val mapping = div(x, int(3))
    val mappedSet = map(mapping, x, set)
    val inMappedSet = in(int(2), mappedSet)

    val state = new SymbState(inMappedSet.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx as boolT).inferType())
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // type inference would reject this
  test("""error: {x: x \in Int}""") {
    val x = name("x") as intT
    val mapSet = map(x, x, intSet())

    val state = new SymbState(mapSet.inferType(), arena, Binding())
    val rewriter = create()
    assertThrows[TlaInputError](rewriter.rewriteUntilDone(state))
  }

  test("""<<2, true>> \in {<<x, y>>: x \in {1,2,3}, y \in {FALSE, TRUE}}""") {
    val set123 = enumSet(1 to 3 map int: _*)
    val setBool = enumSet(bool(false), bool(true))
    val x = name("x") as intT
    val y = name("y") as boolT
    val mapping = tuple(x, y)
    val mappedSet = map(mapping, x, set123, y, setBool)
    val inMappedSet = in(tuple(int(2), bool(true)), mappedSet)

    val state = new SymbState(inMappedSet.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx as boolT).inferType())
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""<<TRUE>> \in {<<y>>: x \in {1,2} \ {2}, y \in {FALSE, TRUE}}""") {
    val x = name("x") as intT
    val y = name("y") as boolT
    val z = name("z") as intT
    // this expression tests regressions in cached expressions
    // we express {1, 2} \ {2} as a filter, as set difference is not in KerA+
    val set12minus2 = filter(z, enumSet(int(1), int(2)), eql(z, int(1)))
    val setBool = enumSet(bool(false), bool(true))
    val boolTuple = parser("<<Bool>>")
    val mapping = tuple(y) as boolTuple
    val mappedSet = map(mapping, x, set12minus2, y, setBool)
    val inMappedSet = in(tuple(bool(true)) as boolTuple, mappedSet)

    val state = new SymbState(inMappedSet.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case membershipEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(membershipEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(membershipEx as boolT).inferType())
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // Regression for the issue 365: https://github.com/informalsystems/apalache/issues/365
  test("""MAP: \E S \in SUBSET { [a: "a", b: 1], [a: "a", b: 2] }:  "a" \in { r.a: r \in S }""") {
    // this test reveals a deep bug in the encoding: SUBSET {[a: 1, b: 1], [a: 1, b: 2]} produces a powerset,
    // whose elements are sets that refer to the same cells,
    // namely the cells for the records [a: 1, b: 1] and [a: 1, b: 2].
    // If one record is included in a subset, but the other is not, then the map rule produced a contradicting constraint
    // for the element "a": it must be in the resulting set, and at the same time it must not be in the resulting set.
    val rec1 = enumFun(str("a"), str("a"), str("b"), int(1))
    val rec2 = enumFun(str("a"), str("a"), str("b"), int(2))
    val base = enumSet(rec1, rec2)
    val powerset = powSet(base)
    val r = name("r") as parser("[a: Str, b: Int]")
    val S = name("S") as parser("Set([a: Str, b: Int])")
    val mapped = map(appFun(r, str("a")), r, S)
    val mem = in(str("a"), mapped)
    val existsForm = apalacheSkolem(exists(S, powerset, mem))

    // the following test goes through without a need for a fix
    val rewriter = create()
    val state = new SymbState(existsForm.inferType(), arena, Binding())
    assumeTlaEx(rewriter, state)

    // the following test captures the core of the functional test in `test/tla/Fix365_ExistsSubset3.tla`,
    // which needed a fix
    // \E S \in SUBSET { [a: "a", b: 1], [a: "a", b: 2] }:  "a" \in { r.a: r \in S } /\ \A x \in S: x.b = 2
    val x = name("x") as parser("[a: Str, b: Int]")
    val forallForm =
      forall(x, S, eql(appFun(x, str("b")), int(2)))
    val existsForm2 = apalacheSkolem(exists(S, powerset, and(mem, forallForm)))
      .inferType()

    // reset the solver and arena
    solverContext = new PreproSolverContext(new Z3SolverContext(SolverConfig.default.copy(debug = true)))
    arena = Arena.create(solverContext)
    val rewriter2 = create()
    val state2 = new SymbState(existsForm2, arena, Binding())
    assumeTlaEx(rewriter2, state2)
  }

  test("""{1, 3} \cup {3, 4} = {1, 3, 4}""") {
    val left = enumSet(int(1), int(3))
    val right = enumSet(int(3), int(4))
    val expected = enumSet(int(1), int(3), int(4))
    val cupSet = cup(left, right)
    val eqExpected = eql(cupSet, expected)

    val state = new SymbState(eqExpected.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        assert(solverContext.sat())
        // check equality
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 2} \subseteq {1, 2, 3} ~~> (true)""") {
    val left = enumSet(int(1), int(2))
    val right = enumSet(int(1), int(2), int(3))
    val ex = subseteq(left, right)

    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 2, 3} \subseteq {1, 2, 3} ~~> (true)""") {
    val right = enumSet(int(1), int(2), int(3))
    val ex = subseteq(right, right)

    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{} \subseteq {1, 2, 3} ~~> (true)""") {
    val right = enumSet(int(1), int(2), int(3))
    // an empty set requires a type annotation
    val ex = subseteq(emptyIntSet, right)

    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""{1, 4} \subseteq {1, 2, 3} ~~> (false)""") {
    val left = enumSet(int(1), int(4))
    val right = enumSet(int(1), int(2), int(3))
    val ex = subseteq(left, right)

    val state = new SymbState(ex.inferType(), arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(rewriter, nextState)
        rewriter.pop()
        rewriter.push()
        solverContext.assertGroundExpr(not(predEx as boolT).inferType())
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""UNION {{1, 2}, {2,3}} = {1, 2, 3}""") {
    val setOf12 = enumSet(int(1), int(2))
    val setOf23 = enumSet(int(3), int(2))
    val setOf123 = enumSet(int(1), int(2), int(3))
    val eq = eql(union(enumSet(setOf12, setOf23)), setOf123)
    val rewriter = create()
    val state = new SymbState(eq.inferType(), arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

}
