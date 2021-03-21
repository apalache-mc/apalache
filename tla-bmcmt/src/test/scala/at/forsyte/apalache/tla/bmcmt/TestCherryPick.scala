package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, Oracle, OracleFactory}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestCherryPick extends RewriterBase with TestingPredefs {
  private val types = Map(
      "b" -> BoolT1(),
      "i" -> IntT1(),
      "i_to_i" -> FunT1(IntT1(), IntT1()),
      "I" -> SetT1(IntT1()),
      "II" -> SetT1(SetT1(IntT1())),
      "Qi" -> SeqT1(IntT1()),
      "ii" -> TupT1(IntT1(), IntT1()),
      "rii" -> RecT1("a" -> IntT1(), "b" -> IntT1()),
      "i_ii" -> TupT1(IntT1(), TupT1(IntT1(), IntT1()))
  )

  private def assertEqWhenChosen(rewriter: SymbStateRewriter, state: SymbState, oracle: Oracle, position: Int,
      expected: TlaEx): SymbState = {
    rewriter.push()
    solverContext.assertGroundExpr(oracle.whenEqualTo(state, position))
    val eq = eql(state.ex, expected).typed(BoolT1())
    assertTlaExAndRestore(rewriter, state.setRex(eq))

    rewriter.pop()
    state
  }

  test("""CHERRY-PICK {1, 2, 2}""") {
    val rewriter = create()
    var state = new SymbState(bool(true).typed(BoolT1()), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 3)
    state = oracleState

    def mkIntCell(i: Int): ArenaCell = {
      // introduce integer cells directly
      arena = state.arena.appendCell(IntT())
      val cell = arena.topCell
      solverContext.assertGroundExpr(eql(cell.toNameEx ? "i", int(i)).typed(types, "b"))
      state = state.setArena(arena)
      cell
    }

    val intCells = Seq(1, 2, 2) map mkIntCell
    val pickedState = new CherryPick(rewriter)
      .pickBasic(IntT(), state, oracle, intCells, state.arena.cellFalse().toNameEx)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, pickedState, oracle, 0, int(1).typed())
    assertEqWhenChosen(rewriter, pickedState, oracle, 1, int(2).typed())
    assertEqWhenChosen(rewriter, pickedState, oracle, 2, int(2).typed())
  }

  test("""CHERRY-PICK {<<1, 2>>, <<3, 4>>}""") {
    val rewriter = create()
    var state = new SymbState(bool(true).typed(), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkTuple(i: Int, j: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tuple(int(i), int(j)).typed(types, "ii")))
      state.asCell
    }

    val tuples = Seq(mkTuple(1, 2), mkTuple(3, 4))
    state = new CherryPick(rewriter)
      .pickTuple(TupleT(Seq(IntT(), IntT())), state, oracle, tuples, state.arena.cellFalse().toNameEx)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, tuples(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, tuples(1).toNameEx)
  }

  test("""CHERRY-PICK {<<1, <<2, 3>> >>, <<3, <<4, 5>> >>}""") {
    val rewriter = create()
    var state = new SymbState(bool(true).typed(), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkTuple(i: Int, j: Int, k: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tuple(int(i), tuple(int(j), int(k)) ? "ii").typed(types, "i_ii")))
      state.asCell
    }

    val tuples = Seq(mkTuple(1, 2, 3), mkTuple(3, 4, 5))
    val tupleT = TupleT(Seq(IntT(), TupleT(Seq(IntT(), IntT()))))
    state = new CherryPick(rewriter).pickTuple(tupleT, state, oracle, tuples, state.arena.cellFalse().toNameEx)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, tuples(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, tuples(1).toNameEx)
  }

  test("""CHERRY-PICK-SEQ {<<1, 2>>, <<3, 4>>}""") {
    val rewriter = create()
    var state = new SymbState(bool(true).typed(BoolT1()), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSeq(args: Int*): ArenaCell = {
      val tup = tuple(args map int: _*)
        .typed(types, "Qi")
      state = rewriter.rewriteUntilDone(state.setRex(tup))
      state.asCell
    }

    val seqs = Seq(mkSeq(1, 2), mkSeq(3, 4))
    state = new CherryPick(rewriter).pickSequence(SeqT(IntT()), state, oracle, seqs, state.arena.cellFalse().toNameEx)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, seqs(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, seqs(1).toNameEx)
  }

  test("""CHERRY-PICK {[a |-> 1, b |-> 2], [a |-> 3, b |-> 4]}""") {
    val rewriter = create()
    var state = new SymbState(bool(true).typed(), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkRecord(i: Int, j: Int): ArenaCell = {
      val rec = enumFun(str("a"), int(i), str("b"), int(j))
        .typed(types, "rii")
      state = rewriter.rewriteUntilDone(state.setRex(rec))
      state.asCell
    }

    val records = Seq(mkRecord(1, 2), mkRecord(3, 4))
    state = new CherryPick(rewriter).pickRecord(records.head.cellType, state, oracle, records,
        state.arena.cellFalse().toNameEx)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, records(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, records(1).toNameEx)
  }

  test("""CHERRY-PICK { {1, 2}, {3, 4} }""") {
    val rewriter = create()
    var state = new SymbState(bool(true).typed(), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(i: Int, j: Int): ArenaCell = {
      val set = enumSet(int(i), int(j))
        .typed(types, "I")
      state = rewriter.rewriteUntilDone(state.setRex(set))
      state.asCell
    }

    val sets = Seq(mkSet(1, 2), mkSet(3, 4))
    state = new CherryPick(rewriter).pickSet(FinSetT(IntT()), state, oracle, sets, state.arena.cellFalse().toNameEx)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, sets(1).toNameEx)
  }

  test("""CHERRY-PICK { {1, 2}, {} }""") {
    val rewriter = create()
    var state = new SymbState(bool(true).typed(), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(setEx: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(setEx))
      state.asCell
    }

    val sets = Seq(mkSet(enumSet(int(1), int(2)).typed(types, "I")), mkSet(enumSet().typed(types, "I")))
    state = new CherryPick(rewriter).pickSet(FinSetT(IntT()), state, oracle, sets, state.arena.cellFalse().toNameEx)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, sets(1).toNameEx)
  }

  test("""CHERRY-PICK { {} }""") {
    val rewriter = create()
    var state = new SymbState(bool(true).typed(), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(setEx: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(setEx))
      state.asCell
    }

    val sets = Seq(mkSet(enumSet().typed(types, "I")))
    state = new CherryPick(rewriter).pickSet(FinSetT(IntT()), state, oracle, sets, state.arena.cellFalse().toNameEx)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
  }

  test("""CHERRY-PICK { {{1, 2}, {3, 4}}, {{5, 6}} }""") {
    val rewriter = create()
    var state = new SymbState(bool(true).typed(), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def rewriteEx(ex: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(ex))
      state.asCell
    }

    val set12 = enumSet(int(1), int(2)) ? "I"
    val set34 = enumSet(int(3), int(4)) ? "I"
    val set56 = enumSet(int(5), int(6)) ? "I"
    val sets =
      Seq(rewriteEx(enumSet(set12, set34).typed(types, "II")), rewriteEx(enumSet(set56).typed(types, "II")))
    state = new CherryPick(rewriter).pickSet(FinSetT(FinSetT(IntT())), state, oracle, sets,
        state.arena.cellFalse().toNameEx)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, sets(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, sets(1).toNameEx)
  }

  test("""CHERRY-PICK { [x \in {1, 2} |-> 2 + x], [x \in {2, 3} |-> 2 * x] }""") {
    val rewriter = create()
    var state = new SymbState(bool(true).typed(), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkFun(dom: BuilderEx, map: BuilderEx): ArenaCell = {
      val fun = funDef(map, name("x") ? "i", dom)
        .typed(types, "i_to_i")
      state = rewriter.rewriteUntilDone(state.setRex(fun))
      state.asCell
    }

    val set12 = enumSet(int(1), int(2)) ? "I"
    val set23 = enumSet(int(2), int(3)) ? "I"
    val fun1 = mkFun(set12, plus(int(2), name("x") ? "i") ? "i")
    val fun2 = mkFun(set23, mult(int(2), name("x") ? "i") ? "i")
    val funs = Seq(fun1, fun2)
    val funT = FunT(FinSetT(IntT()), IntT())
    state = new CherryPick(rewriter).pickFun(funT, state, oracle, funs, state.arena.cellFalse().toNameEx)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, funs(0).toNameEx)
    assertEqWhenChosen(rewriter, state, oracle, 1, funs(1).toNameEx)
  }
}
