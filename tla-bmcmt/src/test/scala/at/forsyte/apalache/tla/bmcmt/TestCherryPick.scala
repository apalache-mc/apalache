package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, Oracle, OracleFactory}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla._
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.types.tla

trait TestCherryPick extends RewriterBase {
  private val parser = DefaultType1Parser

  private val ri = RecT1("a" -> IntT1)
  private val rii = RecT1("a" -> IntT1, "b" -> IntT1)
  private val riis = RecT1("a" -> IntT1, "b" -> IntT1, "c" -> StrT1)

  private def assertEqWhenChosen(
      rewriter: SymbStateRewriter,
      state: SymbState,
      oracle: Oracle,
      position: Int,
      expected: TlaEx): SymbState = {
    rewriter.push()
    solverContext.assertGroundExpr(oracle.whenEqualTo(state, position))
    val eq = eql(unchecked(state.ex), unchecked(expected))
    assertTlaExAndRestore(rewriter, state.setRex(eq))

    rewriter.pop()
    state
  }

  test("""CHERRY-PICK {1, 2, 2}""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 3)
    state = oracleState

    def mkIntCell(i: Int): ArenaCell = {
      // introduce integer cells directly
      arena = state.arena.appendCell(IntT1)
      val cell = arena.topCell
      solverContext.assertGroundExpr(eql(cell.toBuilder, int(i)))
      state = state.setArena(arena)
      cell
    }

    val intCells = Seq(1, 2, 2).map(mkIntCell)
    val pickedState = new CherryPick(rewriter)
      .pickBasic(IntT1, state, oracle, intCells, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, pickedState, oracle, 0, int(1))
    assertEqWhenChosen(rewriter, pickedState, oracle, 1, int(2))
    assertEqWhenChosen(rewriter, pickedState, oracle, 2, int(2))
  }

  test("""CHERRY-PICK {<<1, 2>>, <<3, 4>>}""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkTuple(i: Int, j: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tuple(int(i), int(j))))
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
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkTuple(i: Int, j: Int, k: Int): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(tuple(int(i), tuple(int(j), int(k)))))
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
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSeq(args: BigInt*): ArenaCell = {
      val tup =
        if (args.isEmpty) emptySeq(IntT1)
        else tla.seq(args.map(int): _*)
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
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 3)
    state = oracleState

    def mkSeq(args: BigInt*): ArenaCell = {
      val tup =
        if (args.isEmpty) emptySeq(IntT1)
        else tla.seq(args.map(int): _*)
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
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkRecord(i: Int, j: Int): ArenaCell = {
      val rec = tla.rec("a" -> int(i), "b" -> int(j))
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
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkRecord(i: Int, j: Int): ArenaCell = {
      val rec = tla.rec("a" -> int(i), "b" -> int(j)).map(_.withTag(Typed(recordT)))
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
    val rec1 = rec("a" -> int(1), "b" -> int(2))
    val rec2 = rec("a" -> int(3))

    // introduce an oracle that tells us which element to pick
    val rewriter = create(rewriterType)
    var state = new SymbState(bool(true), arena, Binding())
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
    val rec1 = rec("a" -> int(1), "b" -> int(2))
    val rec2 = rec("a" -> int(3))

    // introduce an oracle that tells us which element to pick
    val rewriter = create(rewriterType)
    var state = new SymbState(bool(true), arena, Binding())
    state = rewriter.rewriteUntilDone(state.setRex(rec1))
    val rec1Cell = state.asCell
    state = rewriter.rewriteUntilDone(state.setRex(rec2))
    val rec2Cell = state.asCell
    val set = enumSet(
        rec1Cell.toBuilder,
        rec2Cell.toBuilder,
    )
    state = rewriter.rewriteUntilDone(state.setRex(set))
    val setCell = state.asCell

    state = new CherryPick(rewriter).pick(setCell, state, bool(false))
    assert(solverContext.sat())
    val result = state.asCell
    // check that the result is equal to one of the records and nothing else
    val eq1 = eql(result.toBuilder, rec1Cell.toBuilder)
    val eq2 = eql(result.toBuilder, rec2Cell.toBuilder)
    val eq1or2 = or(eq1, eq2)
    assertTlaExAndRestore(rewriter, state.setRex(eq1or2))
  }

  test("""CHERRY-PICK { Variant("A", 2), Variant("B", FALSE) }""") { rewriterType: SMTEncoding =>
    val variantT = parser("A(Int) | B(Bool)").asInstanceOf[VariantT1]
    val rewriter = create(rewriterType)
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    state = rewriter.rewriteUntilDone(state.setRex(variant("A", int(33), variantT)))
    val vrtA = state.asCell
    state = rewriter.rewriteUntilDone(state.setRex(variant("B", bool(false), variantT)))
    val vrtB = state.asCell

    val variants @ Seq(a, b) = Seq(vrtA, vrtB)
    state = new CherryPick(rewriter).pickVariant(state, oracle, variants, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK { {1, 2}, {3, 4} }""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(i: BigInt, j: BigInt): ArenaCell = {
      val set = enumSet(int(i), int(j))
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
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(setEx: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(setEx))
      state.asCell
    }

    val sets @ Seq(a, b) = Seq(mkSet(enumSet(int(1), int(2))), mkSet(emptySet(IntT1)))
    state = new CherryPick(rewriter).pickSet(SetT1(IntT1), state, oracle, sets, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK { {} }""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkSet(setEx: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(setEx))
      state.asCell
    }

    val sets @ Seq(a) = Seq(mkSet(emptySet(IntT1)))
    state = new CherryPick(rewriter).pickSet(SetT1(IntT1), state, oracle, sets, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
  }

  test("""CHERRY-PICK { {{1, 2}, {3, 4}}, {{5, 6}} }""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def rewriteEx(ex: TlaEx): ArenaCell = {
      state = rewriter.rewriteUntilDone(state.setRex(ex))
      state.asCell
    }

    val set12 = enumSet(int(1), int(2))
    val set34 = enumSet(int(3), int(4))
    val set56 = enumSet(int(5), int(6))
    val sets @ Seq(a, b) =
      Seq(rewriteEx(enumSet(set12, set34)), rewriteEx(enumSet(set56)))
    state = new CherryPick(rewriter).pickSet(SetT1(SetT1(IntT1)), state, oracle, sets,
        state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, a.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, b.toBuilder)
  }

  test("""CHERRY-PICK { [x \in {1, 2} |-> 2 + x], [x \in {2, 3} |-> 2 * x] }""") { rewriterType: SMTEncoding =>
    val rewriter = create(rewriterType)
    var state = new SymbState(bool(true), arena, Binding())
    // introduce an oracle that tells us which element to pick
    val (oracleState, oracle) = new OracleFactory(rewriter).newConstOracle(state, 2)
    state = oracleState

    def mkFun(dom: TBuilderInstruction, map: TBuilderInstruction): ArenaCell = {
      val fun = funDef(map, name("x", IntT1) -> dom)
      state = rewriter.rewriteUntilDone(state.setRex(fun))
      state.asCell
    }

    val set12 = enumSet(int(1), int(2))
    val set23 = enumSet(int(2), int(3))
    val fun1 = mkFun(set12, plus(int(2), name("x", IntT1)))
    val fun2 = mkFun(set23, mult(int(2), name("x", IntT1)))
    val funs = Seq(fun1, fun2)
    val funT = FunT1(IntT1, IntT1)
    state = new CherryPick(rewriter).pickFun(funT, state, oracle, funs, state.arena.cellFalse().toBuilder)
    assert(solverContext.sat())

    assertEqWhenChosen(rewriter, state, oracle, 0, fun1.toBuilder)
    assertEqWhenChosen(rewriter, state, oracle, 1, fun2.toBuilder)
  }
}
