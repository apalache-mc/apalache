package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser

trait TestSymbStateRewriterVariant extends RewriterBase {
  private val parser = DefaultType1Parser
  private val fieldA = int(33).typed()

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
    expectTaggedValue(rewriter, nextState, cell, "__tag", tla.str(s"Foo").as(StrT1))
  }

  test("""Variant equality""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val vrt1 = variant("Foo", int(33)).as(variantT)
    val vrt2 = variant("Foo", minus(int(44), int(11)).as(IntT1)).as(variantT)

    val state = new SymbState(eql(vrt1, vrt2).as(BoolT1), arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""Variant inequality with different tags""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val vrt1 = variant("Foo", int(33)).as(variantT)
    val vrt2 = variant("Bar", bool(false)).as(variantT)

    val state = new SymbState(not(eql(vrt1, vrt2).as(BoolT1)).as(BoolT1), arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""Variant inequality with different values""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val vrt1 = variant("Foo", int(33)).as(variantT)
    val vrt2 = variant("Foo", int(10)).as(variantT)

    val state = new SymbState(not(eql(vrt1, vrt2).as(BoolT1)).as(BoolT1), arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""VariantGetUnsafe with a right tag""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val vrt1 = variant("Foo", int(33)).as(variantT)
    val unsafe = variantGetUnsafe("Foo", vrt1).as(IntT1)
    val eq = eql(unsafe, int(33)).as(BoolT1)

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""VariantGetUnsafe with a wrong tag""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val vrt2 = variant("Bar", bool(false)).as(variantT)
    val unsafe = variantGetUnsafe("Foo", vrt2).as(IntT1)

    val state = new SymbState(unsafe, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteUntilDone(state)
    // The implementation is free to return any value of the right type (Int).
    // This operator should not make the solver stuck, that is, produce unsatisfiable constraints.
    assert(solverContext.sat())
  }

  test("""VariantGetOrElse with a matching tag""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val vrt1 = variant("Foo", int(33)).as(variantT)
    val value = variantGetOrElse("Foo", vrt1, int(-1)).as(IntT1)
    val eq = eql(value, int(33)).as(BoolT1)

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""VariantGetOrElse with a non-matching tag""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val vrt2 = variant("Bar", bool(false)).as(variantT)
    val value = variantGetOrElse("Foo", vrt2, int(-1)).as(IntT1)
    val eq = eql(value, int(-1)).as(BoolT1)

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""VariantTag""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int)")
    val vrt1 = variant("Foo", int(33)).as(variantT)
    val tag = variantTag(vrt1).as(StrT1)
    val eq = eql(tag, str("Foo")).as(BoolT1)

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""VariantFilter""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val intSetT = parser("Set(Int)")
    val vrt1 = variant("Foo", int(33)).as(variantT)
    val vrt2 = variant("Foo", int(10)).as(variantT)
    val vrt3 = variant("Bar", bool(false)).as(variantT)
    val variantSetT = SetT1(variantT)
    val set = enumSet(vrt1, vrt2, vrt3).as(variantSetT)
    val filtered = variantFilter("Foo", set).as(intSetT)
    val eq = eql(filtered, enumSet(int(33), int(10)).as(intSetT)).as(BoolT1)

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
      expectedValueEx: TlaEx): Unit = {
    val variantOptions = getVariantOptions(cell.cellType)
    val index = (variantOptions.keySet + "__tag").toList.indexOf(tagName)
    val fieldValue = state.arena.getHas(cell)(index)
    val eq = tla.eql(fieldValue.toNameEx, expectedValueEx).as(BoolT1)
    assertTlaExAndRestore(rewriter, state.setRex(eq))
  }
}
