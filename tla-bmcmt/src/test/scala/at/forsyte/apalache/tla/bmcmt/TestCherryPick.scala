package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.config.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.rules.support.{CherryPick, Oracle, OracleFactory}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.types.{BuilderT, tla}

trait TestCherryPick extends RewriterBase {
  private val parser = DefaultType1Parser

  private def assertEqWhenChosen(
      rewriter: SymbStateRewriter,
      state: SymbState,
      oracle: Oracle,
      position: Int,
      expected: BuilderT): SymbState = {
    rewriter.push()
    solverContext.assertGroundExpr(oracle.whenEqualTo(state, position))
    val eq = tla.eql(tla.unchecked(state.ex), expected)
    assertTlaExAndRestore(rewriter, state.setRex(eq))

    rewriter.pop()
    state
  }

  test("""CHERRY-PICK {1, 2, 2}""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 3)
    state = oracleState

    def mkIntCell(i: Int): ArenaCell = {
      // introduce integer cells directly
      arena = state.arena.appendCell(IntT1)
      val cell = arena.topCell
      solverContext.assertGroundExpr(tla.eql(cell.toBuilder, tla.int(i)))
      state = state.setArena(arena)
      cell
    }

    val intCells = Seq(1, 2, 2).map(mkIntCell)
    val pickedState = new CherryPick(rewriter)
      .pickBasic(IntT1, state, oracle, intCells, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, pickedState, oracle, 0, tla.int(1))
    assertEqWhenChosen(rewriter, pickedState, oracle, 1, tla.int(2))
    assertEqWhenChosen(rewriter, pickedState, oracle, 2, tla.int(2))
  }

  test("""CHERRY-PICK {<<1, 2>>, <<3, 4>>}""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkTuple(i: Int, j: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.tuple(tla.int(i), tla.int(j))))
      state.asCell
    }

    val tuples @ Seq(a, b) = Seq(mkTuple(1, 2), mkTuple(3, 4))
    state = new CherryPick(rewriter)
      .pickTuple(TupT1(IntT1, IntT1), state, oracle, tuples, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK {<<1, <<2, 3>> >>, <<3, <<4, 5>> >>}""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkTuple(i: Int, j: Int, k: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tla.tuple(tla.int(i), tla.tuple(tla.int(j), tla.int(k)))))
      state.asCell
    }

    val tuples @ Seq(a, b) = Seq(mkTuple(1, 2, 3), mkTuple(3, 4, 5))
    val tupleT = TupT1(IntT1, TupT1(IntT1, IntT1))
    state = new CherryPick(rewriter).pickTuple(tupleT, state, oracle, tuples, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK-SEQ {<<1, 2>>, <<3, 4>>}""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSeq(args: BigInt*): ArenaCell = {
      val tup =
        if (args.isEmpty) tla.emptySeq(IntT1)
        else tla.seq(args.map(tla.int): _*)
      state = rewriter.rewriteUntilDone(state.setRex(tup))
      state.asCell
    }

    val seqs @ Seq(a, b) = Seq(mkSeq(1, 2), mkSeq(3, 4))
    state = new CherryPick(rewriter).pickSequence(SeqT1(IntT1), state, oracle, seqs, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK-SEQ {<<1, 2>>, <<3, 4, 5>>, <<>>}""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 3)
    state = oracleState

    def mkSeq(args: BigInt*): ArenaCell = {
      val tup =
        if (args.isEmpty) tla.emptySeq(IntT1)
        else tla.seq(args.map(tla.int): _*)
      state = rewriter.rewriteUntilDone(state.setRex(tup))
      state.asCell
    }

    val seqs @ Seq(a, b, c) = Seq(mkSeq(1, 2), mkSeq(3, 4, 5), mkSeq())
    state = new CherryPick(rewriter).pickSequence(SeqT1(IntT1), state, oracle, seqs, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 2, c.toBuilder)
  }

  test("""CHERRY-PICK {[a |-> 1, b |-> 2], [a |-> 3, b |-> 4]}""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkRecord(i: Int, j: Int): ArenaCell = {
      val rec = tla.rec("a" -> tla.int(i), "b" -> tla.int(j))
      state = rewriter.rewriteUntilDone(state.setRex(rec))
      state.asCell
    }

    val records @ Seq(a, b) = Seq(mkRecord(1, 2), mkRecord(3, 4))
    state = new CherryPick(rewriter).pickOldRecord(state, oracle, records, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK { [a |-> 1, b |-> 2], [a |-> 3, b |-> 4]} with rows""") { rewriterType: SMTEncoding =>
    val recordT = parser("{ a: Int, b: Int }")
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkRecord(i: Int, j: Int): ArenaCell = {
      val rec = tla.rec("a" -> tla.int(i), "b" -> tla.int(j)).map(_.withTag(Typed(recordT)))
      state = rewriter.rewriteUntilDone(state.setRex(rec))
      state.asCell
    }

    val records @ Seq(a, b) = Seq(mkRecord(1, 2), mkRecord(3, 4))
    state = new CherryPick(rewriter).pickRecord(state, oracle, records, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK [a |-> 1, b |-> 2] or [a |-> 3]""") { rewriterType: SMTEncoding =>
    // After switching to Snowcat, we allow sets to mix records of compatible types.
    // The old encoding was always introducing spurious fields for all records, as it was extending the records.
    val rec1 = tla.rec("a" -> tla.int(1), "b" -> tla.int(2))
    val rec2 = tla.rec("a" -> tla.int(3))

    // introduce an oracle that tells us which element to pick
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState
    state = rewriter.rewriteUntilDone(state.setRex(rec1))
    val rec1Cell = state.asCell
    state = rewriter.rewriteUntilDone(state.setRex(rec2))
    val rec2Cell = state.asCell

    state = new CherryPick(rewriter).pickOldRecord(state, oracle, Seq(rec1Cell, rec2Cell),
        state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, rec1Cell.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, rec2Cell.toBuilder)
  }

  test("""CHERRY-PICK {[a |-> 1, b |-> 2], [a |-> 3]}""") { rewriterType: SMTEncoding =>
    // After switching to Snowcat, we allow sets to mix records of compatible types.
    // The old encoding was always introducing spurious fields for all records, as it was extending the records.
    val rec1 = tla.rec("a" -> tla.int(1), "b" -> tla.int(2))
    val rec2 = tla.rec("a" -> tla.int(3))

    // introduce an oracle that tells us which element to pick
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    state = rewriter.rewriteUntilDone(state.setRex(rec1))
    val rec1Cell = state.asCell
    state = rewriter.rewriteUntilDone(state.setRex(rec2))
    val rec2Cell = state.asCell
    val set = tla.enumSet(
        rec1Cell.toBuilder,
        rec2Cell.toBuilder,
    )
    state = rewriter.rewriteUntilDone(state.setRex(set))
    val setCell = state.asCell

    state = new CherryPick(rewriter).pick(setCell, state, tla.bool(false))
    assert(solverContext.sat())
    val result = state.asCell
    // check that the result is equal to one of the records and nothing else
    val eq1 = tla.eql(result.toBuilder, rec1Cell.toBuilder)
    val eq2 = tla.eql(result.toBuilder, rec2Cell.toBuilder)
    val eq1or2 = tla.or(eq1, eq2)
    assertTlaExAndRestore(rewriter, state.setRex(eq1or2))
  }

  test("""CHERRY-PICK { Variant("A", 2), Variant("B", FALSE) }""") { rewriterType: SMTEncoding =>
    val variantT = parser("A(Int) | B(Bool)").asInstanceOf[VariantT1]
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    state = rewriter.rewriteUntilDone(state.setRex(tla.variant("A", tla.int(33), variantT)))
    val vrtA = state.asCell
    state = rewriter.rewriteUntilDone(state.setRex(tla.variant("B", tla.bool(false), variantT)))
    val vrtB = state.asCell

    val variants @ Seq(a, b) = Seq(vrtA, vrtB)
    state = new CherryPick(rewriter).pickVariant(state, oracle, variants, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK { {1, 2}, {3, 4} }""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(i: BigInt, j: BigInt): ArenaCell = {
      val set = tla.enumSet(tla.int(i), tla.int(j))
      state = rewriter.rewriteUntilDone(state.setRex(set))
      state.asCell
    }

    val sets @ Seq(a, b) = Seq(mkSet(1, 2), mkSet(3, 4))
    state = new CherryPick(rewriter).pickSet(SetT1(IntT1), state, oracle, sets, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK { {1, 2}, {} }""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(setEx: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(setEx))
      state.asCell
    }

    val sets @ Seq(a, b) = Seq(mkSet(tla.enumSet(tla.int(1), tla.int(2))), mkSet(tla.emptySet(IntT1)))
    state = new CherryPick(rewriter).pickSet(SetT1(IntT1), state, oracle, sets, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK { {} }""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(setEx: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(setEx))
      state.asCell
    }

    val sets @ Seq(a) = Seq(mkSet(tla.emptySet(IntT1)))
    state = new CherryPick(rewriter).pickSet(SetT1(IntT1), state, oracle, sets, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
  }

  test("""CHERRY-PICK { {{1, 2}, {3, 4}}, {{5, 6}} }""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def rewriteEx(ex: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(ex))
      state.asCell
    }

    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val set34 = tla.enumSet(tla.int(3), tla.int(4))
    val set56 = tla.enumSet(tla.int(5), tla.int(6))
    val sets @ Seq(a, b) =
      Seq(rewriteEx(tla.enumSet(set12, set34)), rewriteEx(tla.enumSet(set56)))
    state = new CherryPick(rewriter).pickSet(SetT1(SetT1(IntT1)), state, oracle, sets,
        state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK { [x \in {1, 2} |-> 2 + x], [x \in {2, 3} |-> 2 * x] }""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(tla.bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkFun(dom: BuilderT, map: BuilderT): ArenaCell = {
      val fun = tla.funDef(map, tla.name("x", IntT1) -> dom)
      state = rewriter.rewriteUntilDone(state.setRex(fun))
      state.asCell
    }

    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val set23 = tla.enumSet(tla.int(2), tla.int(3))
    val fun1 = mkFun(set12, tla.plus(tla.int(2), tla.name("x", IntT1)))
    val fun2 = mkFun(set23, tla.mult(tla.int(2), tla.name("x", IntT1)))
    val funs = Seq(fun1, fun2)
    val funT = FunT1(IntT1, IntT1)
    state = new CherryPick(rewriter).pickFun(funT, state, oracle, funs, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, fun1.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, fun2.toBuilder)
  }
}
