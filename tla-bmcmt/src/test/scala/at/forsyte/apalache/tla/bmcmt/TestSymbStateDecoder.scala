package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateDecoder extends RewriterBase {
  private val types = Map(
      "i" -> IntT1(),
      "I" -> SetT1(IntT1()),
      "II" -> SetT1(SetT1(IntT1())),
      "Qi" -> SeqT1(IntT1()),
      "iii" -> TupT1(IntT1(), IntT1(), IntT1()),
      "rib" -> RecT1("a" -> IntT1(), "b" -> BoolT1()),
      "b" -> BoolT1(),
      "i_to_i" -> FunT1(IntT1(), IntT1()),
      "i_TO_i" -> SetT1(FunT1(IntT1(), IntT1()))
  )

  test("decode bool") { rewriterType: String =>
    val originalEx: TlaEx = bool(true).typed()
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
    // hard core comparison
    val eq = eql(decodedEx ? "b", originalEx ? "b")
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode int") { rewriterType: String =>
    val originalEx = int(3).typed()
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
    // hard core comparison
    val eq = eql(decodedEx ? "b", originalEx ? "b")
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode str") { rewriterType: String =>
    val originalEx: TlaEx = str("hello").typed()
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
    // hard core comparison
    val eq = eql(decodedEx, originalEx)
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode Int set") { rewriterType: String =>
    val originalEx = intSet()
      .typed(types, "I")
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
  }

  test("decode Nat set") { rewriterType: String =>
    val originalEx = natSet()
      .typed(types, "I")
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
  }

  test("decode set") { rewriterType: String =>
    val originalEx = enumSet(int(2), int(1), int(2))
      .typed(types, "I")
    val simpleOriginalEx: TlaEx = enumSet(int(1), int(2))
      .typed(types, "I")
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(simpleOriginalEx == decodedEx)
    // hard core comparison
    val eq = eql(decodedEx ? "I", simpleOriginalEx ? "I")
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode fun set") { rewriterType: String =>
    val domEx = enumSet(int(1), int(2))
      .typed(types, "I")
    val cdmEx = enumSet(int(3), int(4))
      .typed(types, "I")
    val originalEx = funSet(domEx, cdmEx)
      .typed(types, "i_TO_i")
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
    // hard core comparison
    val eq = eql(decodedEx, originalEx)
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode SUBSET S") { rewriterType: String =>
    val set = enumSet(int(1), int(2))
      .typed(types, "I")
    val powset = powSet(set)
      .typed(types, "II")
    val state = new SymbState(powset, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(powset == decodedEx)
  }

  test("decode fun") { rewriterType: String =>
    val domEx = enumSet(int(1), int(2))
      .typed(types, "I")
    val funEx = funDef(plus(name("x") ? "i", int(1)) ? "i", name("x") ? "i", domEx)
      .typed(types, "i_to_i")
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    val expectedOutcome: TlaEx =
      atat(colonGreater(int(1), int(2)) ? "i_to_i", colonGreater(int(2), int(3)) ? "i_to_i")
        .typed(types, "i_to_i")
    assert(expectedOutcome == decodedEx)
    val eq = eql(decodedEx, funEx)
      .typed(BoolT1())
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode statically empty fun") { rewriterType: String =>
    val domEx = enumSet() ? "I"
    val funEx = funDef(plus(name("x") ? "i", int(1)) ? "i", name("x") ? "i", domEx)
      .typed(types, "i_to_i")
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    // this is the standard outcome for an empty-domain function: {x \in {} |-> {}}
    val expectedOutcome = funDef(name("x") ? "i", name("x") ? "i", enumSet() ? "I")
      .typed(types, "i_to_i")
    assert(expectedOutcome == decodedEx)
    assertTlaExAndRestore(rewriter, nextState.setRex(eql(decodedEx, funEx).typed(BoolT1())))
  }

  test("decode dynamically empty fun") { rewriterType: String =>
    // this domain is not empty at the arena level, but it is in every SMT model
    def dynEmpty(left: BuilderEx): BuilderEx = {
      filter(name("t") ? "i", left, bool(false) ? "b")
    }

    val domEx = dynEmpty(enumSet(int(1)) ? "I")
      .typed(types, "I")
    // [ x \in {} |-> x + 1 ]
    val funEx = funDef(plus(name("x") ? "i", int(1)) ? "i", name("x") ? "i", domEx)
      .typed(types, "i_to_i")
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    // this is the standard outcome for an empty-domain function: {x \in {} |-> x}
    val expectedOutcome = funDef(name("x") ? "i", name("x") ? "i", enumSet() ? "I")
      .typed(types, "i_to_i")
    assert(expectedOutcome == decodedEx)
    // we cannot directly compare the outcome, as it comes in the same form as a record
    assertTlaExAndRestore(rewriter, nextState.setRex(eql(decodedEx, funEx).typed(BoolT1())))
  }

  test("decode sequence") { rewriterType: String =>
    val seqEx =
      tuple(int(1), int(2), int(3), int(4))
        .typed(types, "Qi")
    val subseqEx = subseq(seqEx, int(2), int(3))
      .typed(types, "Qi")
    val state = new SymbState(subseqEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    val expected = tuple(int(2), int(3))
      .typed(types, "Qi")
    assert(expected == decodedEx)
  }

  test("decode tuple") { rewriterType: String =>
    val tupleEx: TlaEx =
      tuple(int(1), int(2), int(3))
        .typed(types, "iii")
    val state = new SymbState(tupleEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(tupleEx == decodedEx)
  }

  test("decode record") { rewriterType: String =>
    val recEx =
      enumFun(str("a"), int(1), str("b"), bool(true))
        .typed(types, "rib")
    val state = new SymbState(recEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(recEx == decodedEx)
  }
}
