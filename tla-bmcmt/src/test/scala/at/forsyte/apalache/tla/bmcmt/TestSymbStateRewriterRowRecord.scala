package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser

trait TestSymbStateRewriterRowRecord extends RewriterBase {
  private val parser = DefaultType1Parser
  private val fieldA = int(22).typed()
  private val fieldB = bool(false).typed()
  private val fieldC = str("d").typed()

  test("""[a |-> 22, b |-> FALSE, c |-> "d"]""") { rewriterType: SMTEncoding =>
    val recordT = parser("{ a: Int, b: Bool, c: Str }")
    val record = enumFun(str("a"), fieldA, str("b"), fieldB, str("c"), fieldC).as(recordT)

    val state = new SymbState(record, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    assert(recordT == cell.cellType.toTlaType1)

    expectField(rewriter, nextState, cell, "a", fieldA)
    expectField(rewriter, nextState, cell, "b", fieldB)
    expectField(rewriter, nextState, cell, "c", fieldC)
  }

  test("""[a |-> 22, b |-> FALSE, c |-> "d"].a""") { rewriterType: SMTEncoding =>
    val recordT = parser("{ a: Int, b: Bool, c: Str }")
    val record = enumFun(str("a"), fieldA, str("b"), fieldB, str("c"), fieldC).as(recordT)
    val valueOfA = appFun(record, str("a")).as(IntT1)

    val state = new SymbState(valueOfA, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    assert(fieldA.typeTag.asTlaType1() == cell.cellType.toTlaType1)

    val eq = eql(cell.toNameEx, int(22)).as(BoolT1)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""[[a |-> 22, b |-> FALSE, c |-> "d"] EXCEPT !.a = 10]""") { rewriterType: SMTEncoding =>
    val recordT = parser("{ a: Int, b: Bool, c: Str }")
    val record = enumFun(str("a"), fieldA, str("b"), fieldB, str("c"), fieldC).as(recordT)
    val newRecord = except(record, tuple(str("a")).as(TupT1(StrT1)), int(10)).as(recordT)

    val state = new SymbState(newRecord, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    assert(recordT == cell.cellType.toTlaType1)

    expectField(rewriter, nextState, cell, "a", int(10).typed())
    expectField(rewriter, nextState, cell, "b", fieldB)
    expectField(rewriter, nextState, cell, "c", fieldC)
  }

  test("""DOMAIN [a |-> 1, b |-> FALSE, c |-> "d"]""") { rewriterType: SMTEncoding =>
    val recordT = parser("{ a: Int, b: Bool, c: Str }")
    val record = enumFun(str("a"), fieldA, str("b"), fieldB, str("c"), fieldC).as(recordT)
    val domain = dom(record).as(SetT1(StrT1))

    val state = new SymbState(domain, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell

    val eq = eql(cell.toNameEx, enumSet(str("a"), str("b"), str("c")).as(SetT1(StrT1))).as(BoolT1)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("record equality") { rewriterType: SMTEncoding =>
    // order of the fields does not matter
    val recordT = parser("{ a: Int, b: Bool, c: Str }")
    val a = str("a")
    val b = str("b")
    val c = str("c")
    val record1 = enumFun(a, int(1), b, bool(false), c, str("d")).as(recordT)
    val record2 = enumFun(c, str("d"), b, bool(false), a, int(1)).as(recordT)
    val eq = eql(record1, record2).as(BoolT1)
    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("record inequality") { rewriterType: SMTEncoding =>
    // order of the fields does not matter
    val recordT = parser("{ a: Int, b: Bool, c: Str }")
    val a = str("a")
    val b = str("b")
    val c = str("c")
    val record1 = enumFun(a, int(3), b, bool(false), c, str("d")).as(recordT)
    val record2 = enumFun(c, str("d"), b, bool(false), a, int(1)).as(recordT)
    val eq = not(eql(record1, record2).as(BoolT1)).as(BoolT1)
    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  private def getFieldTypes(tp: CellT): Map[String, TlaType1] = {
    tp match {
      case CellTFrom(RecRowT1(RowT1(fieldTypes, None))) =>
        fieldTypes

      case tt =>
        fail("Unexpected type: " + tt)
    }
  }

  private def expectField(
      rewriter: SymbStateRewriter,
      state: SymbState,
      cell: ArenaCell,
      fieldName: String,
      expectedEx: TlaEx): Unit = {
    val fieldTypes = getFieldTypes(cell.cellType)
    val index = fieldTypes.keySet.toList.indexOf(fieldName)
    val fieldValue = state.arena.getHas(cell)(index)
    val eq = tla.eql(fieldValue.toNameEx, expectedEx).as(BoolT1)
    assertTlaExAndRestore(rewriter, state.setRex(eq))
  }
}
