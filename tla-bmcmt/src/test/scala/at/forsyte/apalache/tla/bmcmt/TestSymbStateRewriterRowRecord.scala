package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterRowRecord extends RewriterBase {
  private val parser = DefaultType1Parser
  private val fieldA = tla.int(22)
  private val fieldB = tla.bool(false)
  private val fieldC = tla.str("d")

  test("""[a |-> 22, b |-> FALSE, c |-> "d"]""") { rewriterType: SMTEncoding =>
    val recordT = parser("{ a: Int, b: Bool, c: Str }")
    val record = tla.rowRec(None, "a" -> fieldA, "b" -> fieldB, "c" -> fieldC)

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
    val record = tla.rowRec(None, "a" -> fieldA, "b" -> fieldB, "c" -> fieldC)
    val valueOfA = tla.app(record, tla.str("a"))

    val state = new SymbState(valueOfA, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    assert(typeOf(fieldA.build) == cell.cellType.toTlaType1)

    val eq = tla.eql(tla.unchecked(cell.toNameEx), tla.int(22))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""[[a |-> 22, b |-> FALSE, c |-> "d"] EXCEPT !.a = 10]""") { rewriterType: SMTEncoding =>
    val recordT = parser("{ a: Int, b: Bool, c: Str }")
    val record = tla.rowRec(None, "a" -> fieldA, "b" -> fieldB, "c" -> fieldC)
    val newRecord = tla.except(record, tla.str("a"), tla.int(10))

    val state = new SymbState(newRecord, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    assert(recordT == cell.cellType.toTlaType1)

    expectField(rewriter, nextState, cell, "a", tla.int(10))
    expectField(rewriter, nextState, cell, "b", fieldB)
    expectField(rewriter, nextState, cell, "c", fieldC)
  }

  test("""DOMAIN [a |-> 1, b |-> FALSE, c |-> "d"]""") { rewriterType: SMTEncoding =>
    val record = tla.rowRec(None, "a" -> fieldA, "b" -> fieldB, "c" -> fieldC)
    val domain = tla.dom(record)

    val state = new SymbState(domain, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell

    val eq = tla.eql(tla.unchecked(cell.toNameEx), tla.enumSet(tla.str("a"), tla.str("b"), tla.str("c")))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("record equality") { rewriterType: SMTEncoding =>
    // order of the fields does not matter
    val record1 = tla.rowRec(None, "a" -> tla.int(1), "b" -> tla.bool(false), "c" -> tla.str("d"))
    val record2 = tla.rowRec(None, "c" -> tla.str("d"), "b" -> tla.bool(false), "a" -> tla.int(1))
    val eq = tla.eql(record1, record2)
    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("record inequality") { rewriterType: SMTEncoding =>
    // order of the fields does not matter
    val record1 = tla.rowRec(None, "a" -> tla.int(3), "b" -> tla.bool(false), "c" -> tla.str("d"))
    val record2 = tla.rowRec(None, "c" -> tla.str("d"), "b" -> tla.bool(false), "a" -> tla.int(1))
    val eq = tla.not(tla.eql(record1, record2))
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
      expectedEx: TBuilderInstruction): Unit = {
    val fieldTypes = getFieldTypes(cell.cellType)
    val index = fieldTypes.keySet.toList.indexOf(fieldName)
    val fieldValue = state.arena.getHas(cell)(index)
    val eq = tla.eql(tla.unchecked(fieldValue.toNameEx), expectedEx)
    assertTlaExAndRestore(rewriter, state.setRex(eq))
  }

  private def typeOf(ex: TlaEx): TlaType1 = ex.typeTag match {
    case Typed(tt: TlaType1) => tt
    case tag                 => fail("Expected typed expression, found: " + tag)
  }
}
