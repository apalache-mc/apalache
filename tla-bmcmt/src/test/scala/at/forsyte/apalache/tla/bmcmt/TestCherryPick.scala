package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, Oracle, OracleFactory, OracleHelper}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestCherryPick extends RewriterBase with TestingPredefs {
  private def emptySetWithType(elemT: CellT): TlaEx =
    tla.withType(tla.enumSet(), AnnotationParser.toTla(FinSetT(elemT)))

  private def assertEqWhenChosen(rewriter: SymbStateRewriter, state: SymbState,
                                 oracle: Oracle, position: Int, expected: TlaEx): SymbState = {
    rewriter.push()
    solverContext.assertGroundExpr(oracle.whenEqualTo(state, position))
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
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 3)
    state = oracleState

    def mkIntCell(i: Int): ArenaCell = {
      // introduce integer cells directly
      arena = state.arena.appendCell(IntT())
      val cell = arena.topCell
      solverContext.assertGroundExpr(tla.eql(cell, tla.int(i)))
      state = state.setArena(arena)
      cell
    }

    val intCells = Seq(1, 2, 2) map mkIntCell
    val pickedState = new CherryPick(rewriter)
      .pickBasic(IntT(), state, oracle, intCells, state.arena.cellFalse())
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, pickedState, oracle, 0, tla.int(1))
    assertEqWhenChosen(rewriter, pickedState, oracle, 1, tla.int(2))
    assertEqWhenChosen(rewriter, pickedState, oracle, 2, tla.int(2))
  }

  test("""CHERRY-PICK {<<1, 2>>, <<3, 4>>} ~~> $B$k""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkTuple(i: Int, j: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.tuple(tla.int(i), tla.int(j))))
      state.asCell
    }

    val tuples = Seq(mkTuple(1, 2), mkTuple(3, 4))
    state = new CherryPick(rewriter)
      .pickTuple(TupleT(Seq(IntT(), IntT())), state, oracle, tuples, state.arena.cellFalse())
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, tuples(0))
    assertEqWhenChosen(rewriter, state, oracle, 1, tuples(1))
  }

  test("""CHERRY-PICK {<<1, <<2, 3>> >>, <<3, <<4, 5>> >>} ~~> $B$k""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkTuple(i: Int, j: Int, k: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.tuple(tla.int(i), tla.tuple(tla.int(j), tla.int(k)))))
      state.asCell
    }

    val tuples = Seq(mkTuple(1, 2, 3), mkTuple(3, 4, 5))
    val tupleT = TupleT(Seq(IntT(), TupleT(Seq(IntT(), IntT()))))
    state = new CherryPick(rewriter).pickTuple(tupleT, state, oracle, tuples, state.arena.cellFalse())
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, tuples(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, tuples(1).toNameEx)
  }

  test("""CHERRY-PICK-SEQ {<<1, 2>>, <<3, 4>>}""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSeq(args : Int*): ArenaCell = {
      val tuple = tla.tuple(args map tla.int :_*)
      val annot = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))
      state = rewriter.rewriteUntilDone(state.setRex(annot))
      state.asCell
    }

    val seqs = Seq(mkSeq(1, 2), mkSeq(3, 4))
    state = new CherryPick(rewriter).pickSequence(SeqT(IntT()), state, oracle, seqs, state.arena.cellFalse())
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, seqs(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, seqs(1).toNameEx)
  }

  test("""CHERRY-PICK {[a |-> 1, b |-> 2], [a |-> 3, b |-> 4]} ~~> $B$k""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkRecord(i: Int, j: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.enumFun(tla.str("a"), tla.int(i), tla.str("b"), tla.int(j))))
      state.asCell
    }

    val records = Seq(mkRecord(1, 2), mkRecord(3, 4))
    state = new CherryPick(rewriter).pickRecord(records.head.cellType, state, oracle, records, state.arena.cellFalse())
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, records(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, records(1).toNameEx)
  }

  test("""CHERRY-PICK { {1, 2}, {3, 4} } ~~> $B$k""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(i: Int, j: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.enumSet(tla.int(i), tla.int(j))))
      state.asCell
    }

    val sets = Seq(mkSet(1, 2), mkSet(3, 4))
    state = new CherryPick(rewriter).pickSet(FinSetT(IntT()), state, oracle, sets, state.arena.cellFalse())
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, sets(1).toNameEx)
  }

  test("""CHERRY-PICK { {1, 2}, {} }""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(setEx: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.withType(setEx, AnnotationParser.toTla(FinSetT(IntT())))))
      state.asCell
    }

    val sets = Seq(mkSet(tla.enumSet(1, 2)), mkSet(tla.enumSet()))
    state = new CherryPick(rewriter).pickSet(FinSetT(IntT()), state, oracle, sets, state.arena.cellFalse())
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, sets(1).toNameEx)
  }

  test("""CHERRY-PICK { {} } ~~> $B$k""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(setEx: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(setEx))
      state.asCell
    }

    val sets = Seq(mkSet(tla.enumSet()))
    state = new CherryPick(rewriter).pickSet(FinSetT(IntT()), state, oracle, sets, state.arena.cellFalse())
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
  }

  test("""CHERRY-PICK { {{1, 2}, {3, 4}}, {{5, 6}} }""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def rewriteEx(ex: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(ex))
      state.asCell
    }

    val sets = Seq(rewriteEx(tla.enumSet(tla.enumSet(1, 2),
      tla.enumSet(3, 4))),
      rewriteEx(tla.enumSet(tla.enumSet(5, 6))))
    state = new CherryPick(rewriter).pickSet(FinSetT(FinSetT(IntT())), state, oracle, sets, state.arena.cellFalse())
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, sets(1).toNameEx)
  }

  test("""CHERRY-PICK { [x \in {1, 2} |-> 2 + x], [x \in {2, 3} |-> 2 * x] } ~~> $B$k""") {
    val rewriter = create()
    var state = new SymbState(tla.bool(true), CellTheory(), arena, new Binding)
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkFun(dom: TlaEx, map: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.funDef(map, NameEx("x"), dom)))
      state.asCell
    }

    val fun1 = mkFun(tla.enumSet(1, 2), tla.plus(2, tla.name("x")))
    val fun2 = mkFun(tla.enumSet(2, 3), tla.mult(2, tla.name("x")))
    val funs = Seq(fun1, fun2)
    val funT = FunT(FinSetT(IntT()), IntT())
    state = new CherryPick(rewriter).pickFun(funT, state, oracle, funs, state.arena.cellFalse())
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, funs(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, funs(1).toNameEx)
  }
}
