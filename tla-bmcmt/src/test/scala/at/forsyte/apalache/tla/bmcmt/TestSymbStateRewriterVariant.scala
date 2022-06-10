package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.convenience.tla._

trait TestSymbStateRewriterVariant extends RewriterBase {
  private val tagSort = "__TAG"
  private val parser = DefaultType1Parser
  private val fieldA = int(33).typed()
  private val fieldB = bool(false).typed()
  private val fieldC = str("d").typed()

  test("""Variant("Foo", 33)""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val vrt = variant("Foo", int(33)).as(variantT)

    val state = new SymbState(vrt, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    assert(variantT == cell.cellType.toTlaType1)

    expectTaggedValue(rewriter, nextState, cell, "Foo", fieldA)
    expectTaggedValue(rewriter, nextState, cell, "__tag", tla.str(s"Foo_OF_${tagSort}").as(ConstT1(tagSort)))
  }

  /*
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

   */

  private def getVariantOptions(tp: CellT): Map[String, TlaType1] = {
    tp match {
      case CellTFrom(VariantT1(RowT1(variantOptions, None))) =>
        variantOptions

      case tt =>
        fail("Unexpected type: " + tt)
    }
  }

  private def expectTaggedValue(
      rewriter: SymbStateRewriter,
      state: SymbState,
      cell: ArenaCell,
      tagName: String,
      expectedValueEx: TlaEx): Unit = {
    val variantOptions = getVariantOptions(cell.cellType)
    val index = (variantOptions.keySet + "__tag").toList.indexOf(tagName)
    val fieldValue = state.arena.getHas(cell)(index)
    val eq = tla.eql(fieldValue.toNameEx, expectedValueEx).as(BoolT1)
    assertTlaExAndRestore(rewriter, state.setRex(eq))
  }
}
