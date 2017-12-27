package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterAssignment extends RewriterBase {
  test("""SE-IN-ASSIGN1(int): x \in {1, 2} ~~> TRUE and [x -> $C$k]""") {
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val assign = tla.in(tla.prime(tla.name("x")), set)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    assertUnsatOrExplain(nextState) // should not be possible
  }

  test("""SE-IN-ASSIGN1(set): x \in {{1, 2}, {2, 3}} ~~> TRUE and [x -> $C$k]""") {
    val set = tla.enumSet(tla.enumSet(tla.int(1), tla.int(2)),
                          tla.enumSet(tla.int(2), tla.int(3)))
    val assign = tla.in(tla.prime(tla.name("x")), set)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    val eq12 = tla.eql(boundCell, tla.enumSet(tla.int(1), tla.int(2)))
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
    assertUnsatOrExplain(eqState13) // should not be possible
  }

  test("""SE-IN-ASSIGN1(fun): x \in {[x \in BOOLEAN |-> 0], [x \in BOOLEAN |-> 1]} ~~> TRUE and [x -> $C$k]""") {
    val fun0 = tla.funDef(tla.int(0), tla.name("x"), tla.booleanSet())
    val fun1 = tla.funDef(tla.int(1), tla.name("x"), tla.booleanSet())
    val fun2 = tla.funDef(tla.int(2), tla.name("x"), tla.booleanSet())
    val set = tla.enumSet(fun0, fun1)
    val assign = tla.in(tla.prime(tla.name("x")), set)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    assertUnsatOrExplain(eqStateFun2) // should not be possible
  }

  test("""SE-IN-ASSIGN1(funset): x \in [BOOLEAN -> {0, 1}] ~~> TRUE and [x -> $C$k]""") {
    val fun0 = tla.funDef(tla.int(0), tla.name("x"), tla.booleanSet())
    val fun1 = tla.funDef(tla.int(1), tla.name("x"), tla.booleanSet())
    val fun2 = tla.funDef(tla.int(2), tla.name("x"), tla.booleanSet())
    val set = tla.funSet(tla.booleanSet(), tla.enumSet(tla.int(0), tla.int(1)))
    val assign = tla.in(tla.prime(tla.name("x")), set)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
    assertUnsatOrExplain(eqStateFun2) // should not be possible
  }

  test("""SE-IN-ASSIGN1(funset): x \in [0..(5 - 1) ~~> {FALSE, TRUE}] ~~> TRUE and [x -> $C$k]""") {
    val domain = tla.dotdot(tla.int(0), tla.minus(tla.int(5), tla.int(1)))
    val set = tla.funSet(domain, tla.enumSet(tla.bool(false), tla.bool(true)))
    val assign = tla.in(tla.prime(tla.name("x")), set)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
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
}
