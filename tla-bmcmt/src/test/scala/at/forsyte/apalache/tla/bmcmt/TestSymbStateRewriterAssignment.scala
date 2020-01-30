package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.predef.{TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.BmcOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.{SortedMap, SortedSet, TreeMap}

/**
  * Tests for assignments. The assignments were at the core of Apalache 0.5.x. In Apalache 0.6.x, they are preprocessed
  * into Skolemizable existential quantifiers. We keep the tests for regression.
  */
@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterAssignment extends RewriterBase with TestingPredefs {
  private val set12: OperEx = tla.enumSet(tla.int(1), tla.int(2))
  private val x_prime: OperEx = tla.prime(tla.name("x"))
  private val y_prime: OperEx = tla.prime(tla.name("y"))
  private val boundName: TlaEx = tla.name("t")
  private val boolset: OperEx = tla.enumSet(tla.bool(false), tla.bool(true))

  test("""SE-IN-ASSIGN1(int): \E t \in {1, 2}: x' \in {t} ~~> TRUE and [x -> $C$k]""") {
    val set = set12
    val assign = OperEx(BmcOper.skolemExists, tla.exists(boundName, set, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)

    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat()) // no contradiction introduced

    assertTlaExAndRestore(rewriter, nextState)
    assert(nextState.binding.size == 1)
    assert(nextState.binding.contains("x'"))
    val boundCell = nextState.binding("x'")
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(boundCell, tla.int(1)))
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(boundCell, tla.int(2)))
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(boundCell, tla.int(3)))
    assertUnsatOrExplain(rewriter, nextState) // should not be possible
  }

  test("""SE-IN-ASSIGN1(int): assign in conjunction""") {
    val and =
      tla.and(
        tla.assign(x_prime, tla.int(1)),
        tla.assign(y_prime, tla.int(2))
      )

    val state = new SymbState(and, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    val x_cell = nextState.binding("x'").toNameEx
    val y_cell = nextState.binding("y'").toNameEx

    assert(solverContext.sat()) // no contradiction introduced
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(x_cell, tla.int(1)))
    solverContext.assertGroundExpr(tla.eql(y_cell, tla.int(2)))
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.neql(x_cell, tla.int(1)))
    assertUnsatOrExplain(rewriter, nextState) // should not be possible
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.neql(y_cell, tla.int(2)))
    assertUnsatOrExplain(rewriter, nextState) // should not be possible
  }

  test("""SE-IN-ASSIGN1(int): x' \in {} ~~> FALSE""") {
    val assign = OperEx(BmcOper.skolemExists, tla.exists(boundName, tla.enumSet(), tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(arena.cellFalse().toString == name)
        assert(nextState.binding.isEmpty)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-IN-ASSIGN1(int): \E t \in \in {t_2 \in {1}: FALSE}: x' \in {t} ~~> FALSE""") {
    // a regression test
    def empty(set: TlaEx): TlaEx = {
      tla.filter(tla.name("t_2"),
        set,
        tla.bool(false))
    }

    val assign = OperEx(BmcOper.skolemExists,
      tla.exists(boundName, empty(tla.enumSet(tla.int(1))), tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction should be introduced
    assert(solverContext.sat())
    // the assignment gives us false
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.not(nextState.ex)))
  }

  test("""SE-IN-ASSIGN1(int): x' \in {1} /\ x' = 1 ~~> TRUE and [x -> $C$k]""") {
    val assign = tla.assign(x_prime, tla.int(1))
    val and = tla.and(assign, tla.eql(x_prime, tla.int(1)))

    val state = new SymbState(and, BoolTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(BoolTheory().hasConst(name))
          assert(nextState.binding.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }

    assert(solverContext.sat()) // no contradiction introduced
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assert(!solverContext.sat())
  }

  test("""SE-IN-ASSIGN1(set): \E t \in {{1, 2}, {2, 3}}: x' \in {t} ~~> TRUE and [x -> $C$k]""") {
    val set = tla.enumSet(set12,
      tla.enumSet(tla.int(2), tla.int(3)))
    val assign = OperEx(BmcOper.skolemExists,
      tla.exists(boundName, set, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction introduced
    assert(solverContext.sat())
    // it returns true
    assertTlaExAndRestore(rewriter, nextState)

    assert(nextState.binding.size == 1)
    assert(nextState.binding.contains("x'"))
    val boundCell = nextState.binding("x'")

    // may equal to {1, 2}
    rewriter.push()
    val eq12 = tla.eql(boundCell, set12)
    val eqState12 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq12))
    solverContext.assertGroundExpr(eqState12.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {2, 3}
    rewriter.push()
    val eq23 = tla.eql(boundCell, tla.enumSet(tla.int(2), tla.int(3)))
    val eqState23 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq23))
    solverContext.assertGroundExpr(eqState23.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to {1, 3}
    rewriter.push()
    val eq13 = tla.eql(boundCell, tla.enumSet(tla.int(1), tla.int(3)))
    val eqState13 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq13))
    solverContext.assertGroundExpr(eqState13.ex)
    assertUnsatOrExplain(rewriter, eqState13) // should not be possible
  }

  test("""SE-IN-ASSIGN1(set): \E t \in {{1, 2}, {1+1, 2, 3}} \ {{2, 3}}: x' \in {t} ~~> TRUE and [x -> $C$k]""") {
    // equal elements in different sets mess up picking from a set
    def setminus(left: TlaEx, right: TlaEx): TlaEx = {
      // this is how Keramelizer translates setminus
      tla.filter(tla.name("t_2"),
        left,
        tla.not(tla.eql(tla.name("t_2"), right)))
    }

    val twoSets = tla.enumSet(tla.enumSet(1, 2), tla.enumSet(tla.plus(1, 1), 2, 3))
    val minus = setminus(twoSets, tla.enumSet(2, 3))
    val assign =
      OperEx(BmcOper.skolemExists,
        tla.exists(boundName, minus, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction introduced
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)

    assert(nextState.binding.size == 1)
    assert(nextState.binding.contains("x'"))
    val boundCell = nextState.binding("x'")

    // may equal to {1, 2}
    rewriter.push()
    val eq12 = tla.eql(boundCell, tla.enumSet(1, 2))
    val eqState12 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq12))
    solverContext.assertGroundExpr(eqState12.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // not equal to {1, 3}
    rewriter.push()
    val eq13 = tla.eql(boundCell, tla.enumSet(1, 3))
    val eqState13 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq13))
    solverContext.assertGroundExpr(eqState13.ex)
    assertUnsatOrExplain(rewriter, eqState13) // should not be possible
    rewriter.pop()
    // not equal to {2, 3}
    rewriter.push()
    val eq23 = tla.eql(boundCell, tla.enumSet(2, 3))
    val eqState23 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq23))
    solverContext.assertGroundExpr(eqState23.ex)
    assertUnsatOrExplain(rewriter, eqState23) // should not be possible
    rewriter.pop()
    // 2 is in the result
    rewriter.push()
    val in23 = tla.in(2, boundCell)
    val inState23 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(in23))
    solverContext.assertGroundExpr(inState23.ex)
    assert(solverContext.sat()) // should be possible
    rewriter.pop()
  }

  test("""SE-IN-ASSIGN1(set): \E t \in SUBSET {1, 2}: x' \in {t} ~~> TRUE and [x -> $C$k]""") {
    val set = tla.powSet(set12)
    val assign =
      OperEx(BmcOper.skolemExists,
        tla.exists(boundName, set, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(CellTheory().hasConst(name))
          assert(arena.cellTrue().toString == name)
          assert(nextState.binding.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }

    // no contradiction introduced
    assert(solverContext.sat())
    // may equal to {1, 2}
    rewriter.push()
    val eq12 = tla.eql(boundCell, set12)
    val eqState12 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq12))
    solverContext.assertGroundExpr(eqState12.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {1}
    rewriter.push()
    val eq1 = tla.eql(boundCell, tla.enumSet(tla.int(1)))
    val eqState1 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq1))
    solverContext.assertGroundExpr(eqState1.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {2}
    rewriter.push()
    val eq2 = tla.eql(boundCell, tla.enumSet(tla.int(2)))
    val eqState2 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq2))
    solverContext.assertGroundExpr(eqState2.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {}, but this needs a type annotation
    rewriter.push()
    val eqEmpty = tla.eql(boundCell, tla.withType(tla.enumSet(), AnnotationParser.toTla(FinSetT(IntT()))))
    val eqStateEmpty = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqEmpty))
    solverContext.assertGroundExpr(eqStateEmpty.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // not equal to {1, 2, 3}
    rewriter.push()
    val eq13 = tla.eql(boundCell, tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    val eqState13 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq13))
    solverContext.assertGroundExpr(eqState13.ex)
    assertUnsatOrExplain(rewriter, eqState13) // should not be possible
  }

  test("""SE-IN-ASSIGN1(fun): \E t \in {[x \in BOOLEAN |-> 0], [x2 \in BOOLEAN |-> 1]}: x' \in {t} ~~> TRUE""") {
    val fun0 = tla.funDef(tla.int(0), tla.name("x2"), tla.booleanSet())
    val fun1 = tla.funDef(tla.int(1), tla.name("x3"), tla.booleanSet())
    val fun2 = tla.funDef(tla.int(2), tla.name("x4"), tla.booleanSet())
    val set = tla.enumSet(fun0, fun1)
    val assign =
      OperEx(BmcOper.skolemExists,
        tla.exists(boundName, set, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction introduced
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
    assert(nextState.binding.size == 1)
    assert(nextState.binding.contains("x'"))
    val boundCell = nextState.binding("x'")

    // may equal to fun0
    rewriter.push()
    val eqFun0 = tla.eql(boundCell, fun0)
    val eqStateFun0 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun0))
    solverContext.assertGroundExpr(eqStateFun0.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to fun1
    rewriter.push()
    val eqFun1 = tla.eql(boundCell, fun1)
    val eqStateFun1 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun1))
    solverContext.assertGroundExpr(eqStateFun1.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to fun2
    rewriter.push()
    val eqFun2 = tla.eql(boundCell, fun2)
    val eqStateFun2 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun2))
    solverContext.assertGroundExpr(eqStateFun2.ex)
    assertUnsatOrExplain(rewriter, eqStateFun2) // should not be possible
  }

  test("""SE-IN-ASSIGN1(funset): \E t \in [BOOLEAN -> {0, 1}]: x' \in {t} ~~> TRUE""") {
    val fun0 = tla.funDef(tla.int(0), tla.name("x"), tla.booleanSet())
    val fun1 = tla.funDef(tla.int(1), tla.name("x"), tla.booleanSet())
    val fun2 = tla.funDef(tla.int(2), tla.name("x"), tla.booleanSet())
    val set = tla.funSet(tla.booleanSet(), tla.enumSet(tla.int(0), tla.int(1)))
    val assign =
      OperEx(BmcOper.skolemExists,
        tla.exists(boundName, set, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(CellTheory().hasConst(name))
          assert(arena.cellTrue().toString == name)
          assert(nextState.binding.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }

    // no contradiction introduced
    assert(solverContext.sat())
    // may equal to fun0
    rewriter.push()
    val eqFun0 = tla.eql(boundCell, fun0)
    val eqStateFun0 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun0))
    solverContext.assertGroundExpr(eqStateFun0.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to fun1
    rewriter.push()
    val eqFun1 = tla.eql(boundCell, fun1)
    val eqStateFun1 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun1))
    solverContext.assertGroundExpr(eqStateFun1.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to fun2
    rewriter.push()
    val eqFun2 = tla.eql(boundCell, fun2)
    val eqStateFun2 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun2))
    solverContext.assertGroundExpr(eqStateFun2.ex)
    assertUnsatOrExplain(rewriter, eqStateFun2) // should not be possible
  }

  test("""SE-IN-ASSIGN1(funset): \E t \in [{} -> {0, 1}]: x' \in {t} ~~> FALSE""") {
    // regression
    val set = tla.funSet(tla.enumSet(), tla.enumSet(tla.int(0), tla.int(1)))
    val assign =
      OperEx(BmcOper.skolemExists,
        tla.exists(boundName, set, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction introduced
    assert(solverContext.sat())
    // The assignment rule returns a function that is defined on the empty set.
    // It's probably similar to an empty set. In fact, the associated relation is empty.
    assertTlaExAndRestore(rewriter, nextState)
  }

  test("""SE-IN-ASSIGN1(funset): \E t \in [0..(5 - 1) -> BOOLEAN]: x' \in {t} ~~> TRUE""") {
    val domain = tla.dotdot(tla.int(0), tla.minus(tla.int(5), tla.int(1)))
    val set = tla.funSet(domain, boolset)
    val assign =
      OperEx(BmcOper.skolemExists,
        tla.exists(boundName, set, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(CellTheory().hasConst(name))
          assert(arena.cellTrue().toString == name)
          assert(nextState.binding.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }
  }

  test("""SE-IN-ASSIGN(funset with Nat): \E t \in [0..4 -> Nat]: x' \in {t}""") {
    val domain = tla.dotdot(tla.int(0), tla.int(4))
    val set = tla.funSet(domain, ValEx(TlaNatSet))
    val assign =
      OperEx(BmcOper.skolemExists,
        tla.exists(boundName, set, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(rewriter.solverContext.sat())
    val x = nextState.binding("x'")
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.ge(tla.appFun(x, tla.int(1)), 0)))
  }

  test("""SE-IN-ASSIGN(funset with Int): \E t \in [0..4 -> Int]: x' \in {t}""") {
    val domain = tla.dotdot(tla.int(0), tla.int(4))
    val set = tla.funSet(domain, ValEx(TlaIntSet))
    val assign =
      OperEx(BmcOper.skolemExists,
        tla.exists(boundName, set, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(rewriter.solverContext.sat())
    // there is not much to check here, since it is just a function that returns an integer
  }

  // the model checker will never meet such an expression, as it will be optimized into several existentials by ExprOptimizer
  test("""SE-IN-ASSIGN1(tuple): \E t \in {<<1, FALSE, {1, 3}>>, <<2, TRUE, {4}>>}: x' \in {t}""") {
    val set1 = tla.enumSet(tla.int(1), tla.int(3))
    val tuple1 = tla.tuple(tla.int(1), tla.bool(false), set1)
    val set2 = tla.enumSet(tla.int(4))
    val tuple2 = tla.tuple(tla.int(2), tla.bool(true), set2)
    val set = tla.enumSet(tuple1, tuple2)
    val assign =
      OperEx(BmcOper.skolemExists,
        tla.exists(boundName, set, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        val cell = nextState.binding("x'")
        assert(TupleT(List(IntT(), BoolT(), FinSetT(IntT()))) == cell.cellType)

        val membershipTest =
          tla.and(tla.in(tla.appFun(x_prime, tla.int(1)),
            set12),
            tla.in(tla.appFun(x_prime, tla.int(2)),
              boolset),
            tla.in(tla.appFun(x_prime, tla.int(3)),
              tla.enumSet(set1, set2))
          ) ///

        assertTlaExAndRestore(rewriter, nextState.setRex(membershipTest))

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  // the model checker will never meet such an expression, as it will be optimized into several existentials by ExprOptimizer
  test("""SE-IN-ASSIGN1(record): \E t \in {{"a" -> 1, "b" -> FALSE}, {"a" -> 2, "b" -> TRUE, "c" -> {3, 4}}}: x' \in {t}""") {
    val annotation = AnnotationParser.toTla(RecordT(SortedMap("a" -> IntT(), "b" -> BoolT(), "c" -> FinSetT(IntT()))))
    // records in a set can have different sets of keys, although the field types should be compatible for each field
    val record1 = tla.enumFun(tla.str("a"), tla.int(1),
      tla.str("b"), tla.bool(false))
    val set34 = tla.enumSet(tla.int(3), tla.int(4))
    val record2 = tla.enumFun(tla.str("a"), tla.int(2),
      tla.str("b"), tla.bool(true), tla.str("c"), set34)
    val recordSet = tla.enumSet(tla.withType(record1, annotation), record2)
    val assign =
      OperEx(BmcOper.skolemExists,
        tla.exists(boundName, recordSet, tla.assign(x_prime, boundName)))

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
    rewriter.typeFinder.inferAndSave(assign) // trigger type inference manually
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        val cell = nextState.binding("x'")
        // x' is assigned a record from recordSet
        assert(cell.cellType.isInstanceOf[RecordT])
        assert(cell.cellType.asInstanceOf[RecordT].fields
          == TreeMap("a" -> IntT(), "b" -> BoolT(), "c" -> FinSetT(IntT())))

        val a_of_x_prime = tla.appFun(x_prime, tla.str("a"))
        val b_of_x_prime = tla.appFun(x_prime, tla.str("b"))
        val c_of_x_prime = tla.appFun(x_prime, tla.str("c"))
        val membershipTest =
          tla.and(
            tla.in(a_of_x_prime, set12),
            tla.in(b_of_x_prime, boolset))
        // interestingly, we cannot expect that x'.c \in { 3, 4 },
        // as the value of the field c is unknown for the first record
        //            tla.in(c_of_x_prime, tla.enumSet(set34))

        assertTlaExAndRestore(rewriter, nextState.setRex(membershipTest))

        // if we assume that result["a"] = 2, we should get result["b"] = TRUE, and result["c"] = { 3, 4 }
        rewriter.push()
        val assumption = tla.eql(a_of_x_prime, tla.int(2))
        val assumState = assumeTlaEx(rewriter, nextState.setRex(assumption))

        val bIsTrue = tla.eql(b_of_x_prime, tla.bool(true))
        assertTlaExAndRestore(rewriter, assumState.setRex(bIsTrue))
        val cIsSet34 = tla.eql(c_of_x_prime, set34)
        assertTlaExAndRestore(rewriter, assumState.setRex(cIsSet34))
        rewriter.pop()

        // if we assume that result["a"] = 1, we should get DOMAIN result = {"a", "b"}
        rewriter.push()
        val assumption2 = tla.eql(a_of_x_prime, tla.int(1))
        val assumeState2 = assumeTlaEx(rewriter, nextState.setRex(assumption2))
        val (newArena, expectedDom) =
          rewriter.recordDomainCache.getOrCreate(assumeState2.arena, (SortedSet("a", "b"), SortedSet("c")))
        val domEq = tla.eql(expectedDom, tla.dom(x_prime))
        assertTlaExAndRestore(rewriter, assumeState2.setArena(newArena).setRex(domEq))
        // and check that the record equals to the expected one
        val eq = tla.eql(tla.withType(record1, annotation), x_prime)
        assertTlaExAndRestore(rewriter, assumeState2.setRex(eq))
        rewriter.pop()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
