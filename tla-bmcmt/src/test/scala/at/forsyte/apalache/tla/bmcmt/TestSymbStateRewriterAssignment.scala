package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TestingPredefs}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.{SortedMap, SortedSet, TreeMap}

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterAssignment extends RewriterBase with TestingPredefs {
  private val set12: OperEx = tla.enumSet(tla.int(1), tla.int(2))
  private val x_prime: OperEx = tla.prime(tla.name("x"))

  test("""SE-IN-ASSIGN1(int): x' \in {1, 2} ~~> TRUE and [x -> $C$k]""") {
    val set = set12
    val assign = tla.in(x_prime, set)

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

    assert(solverContext.sat()) // no contradiction introduced
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

  test("""SE-IN-ASSIGN1(int): x' \in {} ~~> FALSE""") {
    val assign = tla.in(x_prime, tla.enumSet())

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

  test("""SE-IN-ASSIGN1(int): x' \in {1} /\ x' = 1 ~~> TRUE and [x -> $C$k]""") {
    val set = tla.enumSet(tla.int(1))
    val assign = tla.in(x_prime, set)
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

  test("""SE-IN-ASSIGN1(set): x' \in {{1, 2}, {2, 3}} ~~> TRUE and [x -> $C$k]""") {
    val set = tla.enumSet(set12,
      tla.enumSet(tla.int(2), tla.int(3)))
    val assign = tla.in(x_prime, set)

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

  test("""SE-IN-ASSIGN1(set): x' \in {{1, 2}, {1+1, 2, 3}} \ {{2, 3}} ~~> TRUE and [x -> $C$k]""") {
    // equal elements in different sets mess up picking from a set
    val twoSets = tla.enumSet(tla.enumSet(1, 2), tla.enumSet(tla.plus(1, 1), 2, 3))
    val minus = tla.setminus(twoSets, tla.enumSet(tla.enumSet(2, 3)))
    val assign = tla.in(tla.prime("x"), minus)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = createWithoutCache() // it is critical that 1+1 does not get simplified
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

  test("""SE-IN-ASSIGN1(set): x' \in SUBSET {1, 2} ~~> TRUE and [x -> $C$k]""") {
    val set = tla.powSet(set12)
    val assign = tla.in(x_prime, set)

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

  test("""SE-IN-ASSIGN1(fun): x' \in {[x \in BOOLEAN |-> 0], [x2 \in BOOLEAN |-> 1]} ~~> TRUE and [x -> $C$k]""") {
    val fun0 = tla.funDef(tla.int(0), tla.name("x2"), tla.booleanSet())
    val fun1 = tla.funDef(tla.int(1), tla.name("x3"), tla.booleanSet())
    val fun2 = tla.funDef(tla.int(2), tla.name("x4"), tla.booleanSet())
    val set = tla.enumSet(fun0, fun1)
    val assign = tla.in(x_prime, set)

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

  test("""SE-IN-ASSIGN1(funset): x' \in [BOOLEAN -> {0, 1}] ~~> TRUE and [x -> $C$k]""") {
    val fun0 = tla.funDef(tla.int(0), tla.name("x"), tla.booleanSet())
    val fun1 = tla.funDef(tla.int(1), tla.name("x"), tla.booleanSet())
    val fun2 = tla.funDef(tla.int(2), tla.name("x"), tla.booleanSet())
    val set = tla.funSet(tla.booleanSet(), tla.enumSet(tla.int(0), tla.int(1)))
    val assign = tla.in(x_prime, set)

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

  private val boolset: OperEx = tla.enumSet(tla.bool(false), tla.bool(true))
  test("""SE-IN-ASSIGN1(funset): x' \in [0..(5 - 1) ~~> {FALSE, TRUE}] ~~> TRUE and [x -> $C$k]""") {
    val domain = tla.dotdot(tla.int(0), tla.minus(tla.int(5), tla.int(1)))
    val set = tla.funSet(domain, boolset)
    val assign = tla.in(x_prime, set)

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

  test("""SE-IN-ASSIGN1(tuple): x' \in {<<1, FALSE, {1, 3}>>, <<2, TRUE, {4}>>} ~~> [x -> $C$k]""") {
    val set1 = tla.enumSet(tla.int(1), tla.int(3))
    val tuple1 = tla.tuple(tla.int(1), tla.bool(false), set1)
    val set2 = tla.enumSet(tla.int(4))
    val tuple2 = tla.tuple(tla.int(2), tla.bool(true), set2)
    val set = tla.enumSet(tuple1, tuple2)
    val assign = tla.in(x_prime, set)

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

  test("""SE-IN-ASSIGN1(record): x' \in {{"a" -> 1, "b" -> FALSE}, {"a" -> 2, "b" -> TRUE, "c" -> {3, 4}}} ~~> [x -> $C$k]""") {
    // records in a set can have different sets of keys, although the field types should be compatible for each field
    val record1 = tla.enumFun(tla.str("a"), tla.int(1),
      tla.str("b"), tla.bool(false))
    val set34 = tla.enumSet(tla.int(3), tla.int(4))
    val record2 = tla.enumFun(tla.str("a"), tla.int(2),
      tla.str("b"), tla.bool(true), tla.str("c"), set34)
    val annotation = AnnotationParser.toTla(RecordT(SortedMap("a" -> IntT(), "b" -> BoolT(),  "c" -> FinSetT(IntT()))))
    val recordSet = tla.enumSet(tla.withType(record1, annotation), record2)
    val assign = tla.in(x_prime, recordSet)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = create()
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
          rewriter.recordDomainCache.getOrCreate(assumeState2.arena, SortedSet("a", "b"))
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
