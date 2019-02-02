package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestCherryPick extends RewriterBase with TestingPredefs {
  private def emptySetWithType(elemT: CellT): TlaEx =
    tla.withType(tla.enumSet(), AnnotationParser.toTla(FinSetT(elemT)))

  private def assertEqWhenChosen(rewriter: SymbStateRewriter, state: SymbState,
                                 oracle: NameEx, oracleValue: Int, expected: TlaEx): SymbState = {
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(oracle, tla.int(oracleValue)))
    val ns = rewriter.rewriteUntilDone(state.setRex(tla.eql(state.ex, expected)))
    rewriter.push()
    solverContext.assertGroundExpr(ns.ex)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(ns.ex))
    assertUnsatOrExplain(rewriter, ns)
    rewriter.pop()
    rewriter.pop()
    state
  }

  test("""CHERRY-PICK {1, 2, 2} ~~> $B$k""") {
    val rewriter = create()
    // introduce an oracle that tells us which element to pick
    arena = arena.appendCell(IntT())
    val oracle = arena.topCell.toNameEx
    solverContext.assertGroundExpr(tla.ge(oracle, tla.int(0)))
    solverContext.assertGroundExpr(tla.lt(oracle, tla.int(3)))
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)

    def mkIntCell(i: Int): ArenaCell = {
      // introduce integer cells directly
      arena = state.arena.appendCell(IntT())
      val cell = arena.topCell
      solverContext.assertGroundExpr(tla.eql(cell.toNameEx, tla.int(i)))
      state = state.setArena(arena)
      cell
    }

    val intCells = Seq(1, 2, 2) map mkIntCell
    val pickedState = new CherryPick(rewriter).pickBasic(IntT(), state, oracle, intCells)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, pickedState, oracle, 0, tla.int(1))
    assertEqWhenChosen(rewriter, pickedState, oracle, 1, tla.int(2))
    assertEqWhenChosen(rewriter, pickedState, oracle, 2, tla.int(2))
  }

  test("""CHERRY-PICK {<<1, 2>>, <<3, 4>>} ~~> $B$k""") {
    val rewriter = create()
    // introduce an oracle that tells us which element to pick
    arena = arena.appendCell(IntT())
    val oracle = arena.topCell.toNameEx
    solverContext.assertGroundExpr(tla.ge(oracle, tla.int(0)))
    solverContext.assertGroundExpr(tla.lt(oracle, tla.int(2)))
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)

    def mkTuple(i: Int, j: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.tuple(tla.int(i), tla.int(j))))
      state.asCell
    }

    val tuples = Seq(mkTuple(1, 2), mkTuple(3, 4))
    state = new CherryPick(rewriter).pickTuple(TupleT(Seq(IntT(), IntT())), state, oracle, tuples)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, tuples(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, tuples(1).toNameEx)
  }

  test("""CHERRY-PICK {<<1, <<2, 3>> >>, <<3, <<4, 5>> >>} ~~> $B$k""") {
    val rewriter = create()
    // introduce an oracle that tells us which element to pick
    arena = arena.appendCell(IntT())
    val oracle = arena.topCell.toNameEx
    solverContext.assertGroundExpr(tla.ge(oracle, tla.int(0)))
    solverContext.assertGroundExpr(tla.lt(oracle, tla.int(2)))
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)

    def mkTuple(i: Int, j: Int, k: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.tuple(tla.int(i), tla.tuple(tla.int(j), tla.int(k)))))
      state.asCell
    }

    val tuples = Seq(mkTuple(1, 2, 3), mkTuple(3, 4, 5))
    val tupleT = TupleT(Seq(IntT(), TupleT(Seq(IntT(), IntT()))))
    state = new CherryPick(rewriter).pickTuple(tupleT, state, oracle, tuples)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, tuples(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, tuples(1).toNameEx)
  }

  test("""CHERRY-PICK {[a |-> 1, b |-> 2], [a |-> 3, b |-> 4]} ~~> $B$k""") {
    val rewriter = create()
    // introduce an oracle that tells us which element to pick
    arena = arena.appendCell(IntT())
    val oracle = arena.topCell.toNameEx
    solverContext.assertGroundExpr(tla.ge(oracle, tla.int(0)))
    solverContext.assertGroundExpr(tla.lt(oracle, tla.int(2)))
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)

    def mkRecord(i: Int, j: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.enumFun(tla.str("a"), tla.int(i), tla.str("b"), tla.int(j))))
      state.asCell
    }

    val records = Seq(mkRecord(1, 2), mkRecord(3, 4))
    state = new CherryPick(rewriter).pickRecord(records.head.cellType, state, oracle, records)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, records(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, records(1).toNameEx)
  }

  test("""CHERRY-PICK { {1, 2}, {3, 4} } ~~> $B$k""") {
    val rewriter = create()
    // introduce an oracle that tells us which element to pick
    arena = arena.appendCell(IntT())
    val oracle = arena.topCell.toNameEx
    solverContext.assertGroundExpr(tla.ge(oracle, tla.int(0)))
    solverContext.assertGroundExpr(tla.lt(oracle, tla.int(2)))
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)

    def mkSet(i: Int, j: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.enumSet(tla.int(i), tla.int(j))))
      state.asCell
    }

    val sets = Seq(mkSet(1, 2), mkSet(3, 4))
    state = new CherryPick(rewriter).pickSet(FinSetT(IntT()), state, oracle, sets)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, sets(1).toNameEx)
  }

  test("""CHERRY-PICK { {1, 2}, {} } ~~> $B$k""") {
    val rewriter = create()
    // introduce an oracle that tells us which element to pick
    arena = arena.appendCell(IntT())
    val oracle = arena.topCell.toNameEx
    solverContext.assertGroundExpr(tla.ge(oracle, tla.int(0)))
    solverContext.assertGroundExpr(tla.lt(oracle, tla.int(2)))
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)

    def mkSet(setEx: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.withType(setEx, AnnotationParser.toTla(FinSetT(IntT())))))
      state.asCell
    }

    val sets = Seq(mkSet(tla.enumSet(1, 2)), mkSet(tla.enumSet()))
    state = new CherryPick(rewriter).pickSet(FinSetT(IntT()), state, oracle, sets)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, sets(1).toNameEx)
  }

  test("""CHERRY-PICK { {} } ~~> $B$k""") {
    val rewriter = create()
    // introduce an oracle that tells us which element to pick
    arena = arena.appendCell(IntT())
    val oracle = arena.topCell.toNameEx
    solverContext.assertGroundExpr(tla.ge(oracle, tla.int(0)))
    solverContext.assertGroundExpr(tla.lt(oracle, tla.int(1)))
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)

    def mkSet(setEx: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(setEx))
      state.asCell
    }

    val sets = Seq(mkSet(tla.enumSet()))
    state = new CherryPick(rewriter).pickSet(FinSetT(IntT()), state, oracle, sets)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
  }

  test("""CHERRY-PICK { {{1, 2}, {3, 4}}, {{5, 6}} } ~~> $B$k""") {
    val rewriter = create()
    // introduce an oracle that tells us which element to pick
    arena = arena.appendCell(IntT())
    val oracle = arena.topCell.toNameEx
    solverContext.assertGroundExpr(tla.ge(oracle, tla.int(0)))
    solverContext.assertGroundExpr(tla.lt(oracle, tla.int(2)))
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)

    def rewriteEx(ex: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(ex))
      state.asCell
    }

    val sets = Seq(rewriteEx(tla.enumSet(tla.enumSet(1, 2),
      tla.enumSet(3, 4))),
      rewriteEx(tla.enumSet(tla.enumSet(5, 6))))
    state = new CherryPick(rewriter).pickSet(FinSetT(FinSetT(IntT())), state, oracle, sets)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, sets(1).toNameEx)
  }

  test("""CHERRY-PICK { [x \in {1, 2} |-> 2 + x], [x \in {2, 3} |-> 2 * x] } ~~> $B$k""") {
    val rewriter = create()
    // introduce an oracle that tells us which element to pick
    arena = arena.appendCell(IntT())
    val oracle = arena.topCell.toNameEx
    solverContext.assertGroundExpr(tla.ge(oracle, tla.int(0)))
    solverContext.assertGroundExpr(tla.lt(oracle, tla.int(2)))
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)

    def mkFun(dom: TlaEx, map: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.funDef(map, NameEx("x"), dom)))
      state.asCell
    }

    val fun1 = mkFun(tla.enumSet(1, 2), tla.plus(2, tla.name("x")))
    val fun2 = mkFun(tla.enumSet(2, 3), tla.mult(2, tla.name("x")))
    val funs = Seq(fun1, fun2)
    val funT = FunT(FinSetT(IntT()), IntT())
    state = new CherryPick(rewriter).pickFun(funT, state, oracle, funs)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, funs(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, funs(1).toNameEx)
  }
}
