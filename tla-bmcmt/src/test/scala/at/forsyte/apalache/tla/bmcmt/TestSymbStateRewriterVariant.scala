package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterVariant extends RewriterBase {
  private val parser = DefaultType1Parser
  private val fieldA = tla.int(33)

  test("""Variant("Foo", 33)""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)").asInstanceOf[VariantT1]
    val vrt = tla.variant("Foo", tla.int(33), variantT)

    val state = new SymbState(vrt, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    assert(variantT == cell.cellType.toTlaType1)

    expectTaggedValue(rewriter, nextState, cell, "Foo", fieldA)
    expectTaggedValue(rewriter, nextState, cell, "__tag", tla.str("Foo"))
  }

  test("""Variant equality""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)").asInstanceOf[VariantT1]
    val vrt1 = tla.variant("Foo", tla.int(33), variantT)
    val vrt2 = tla.variant("Foo", tla.minus(tla.int(44), tla.int(11)), variantT)

    val state = new SymbState(tla.eql(vrt1, vrt2), arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""Variant inequality with different tags""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)").asInstanceOf[VariantT1]
    val vrt1 = tla.variant("Foo", tla.int(33), variantT)
    val vrt2 = tla.variant("Bar", tla.bool(false), variantT)

    val state = new SymbState(tla.not(tla.eql(vrt1, vrt2)), arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""Variant inequality with different values""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)").asInstanceOf[VariantT1]
    val vrt1 = tla.variant("Foo", tla.int(33), variantT)
    val vrt2 = tla.variant("Foo", tla.int(10), variantT)

    val state = new SymbState(tla.not(tla.eql(vrt1, vrt2)), arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""VariantGetUnsafe with a right tag""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)").asInstanceOf[VariantT1]
    val vrt1 = tla.variant("Foo", tla.int(33), variantT)
    val unsafe = tla.variantGetUnsafe("Foo", vrt1)
    val eq = tla.eql(unsafe, tla.int(33))

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""VariantGetUnsafe with a wrong tag""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)").asInstanceOf[VariantT1]
    val vrt2 = tla.variant("Bar", tla.bool(false), variantT)
    val unsafe = tla.variantGetUnsafe("Foo", vrt2)

    val state = new SymbState(unsafe, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteUntilDone(state)
    // The implementation is free to return any value of the right type (Int).
    // This operator should not make the solver stuck, that is, produce unsatisfiable constraints.
    assert(solverContext.sat())
  }

  test("""VariantGetOrElse with a matching tag""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)").asInstanceOf[VariantT1]
    val vrt1 = tla.variant("Foo", tla.int(33), variantT)
    val value = tla.variantGetOrElse("Foo", vrt1, tla.int(-1))
    val eq = tla.eql(value, tla.int(33))

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""VariantGetOrElse with a non-matching tag""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)").asInstanceOf[VariantT1]
    val vrt2 = tla.variant("Bar", tla.bool(false), variantT)
    val value = tla.variantGetOrElse("Foo", vrt2, tla.int(-1))
    val eq = tla.eql(value, tla.int(-1))

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""VariantTag""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int)").asInstanceOf[VariantT1]
    val vrt1 = tla.variant("Foo", tla.int(33), variantT)
    val tag = tla.variantTag(vrt1)
    val eq = tla.eql(tag, tla.str("Foo"))

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""VariantFilter""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)").asInstanceOf[VariantT1]
    val vrt1 = tla.variant("Foo", tla.int(33), variantT)
    val vrt2 = tla.variant("Foo", tla.int(10), variantT)
    val vrt3 = tla.variant("Bar", tla.bool(false), variantT)
    val set = tla.enumSet(vrt1, vrt2, vrt3)
    val filtered = tla.variantFilter("Foo", set)
    val eq = tla.eql(filtered, tla.enumSet(tla.int(33), tla.int(10)))

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

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
      expectedValueEx: TBuilderInstruction): Unit = {
    val variantOptions = getVariantOptions(cell.cellType)
    val index = (variantOptions.keySet + "__tag").toList.indexOf(tagName)
    val fieldValue = state.arena.getHas(cell)(index)
    val eq = tla.eql(tla.unchecked(fieldValue.toNameEx), expectedValueEx)
    assertTlaExAndRestore(rewriter, state.setRex(eq))
  }
}
