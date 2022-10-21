package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser

trait TestSymbStateDecoder extends RewriterBase {
  private val parser = DefaultType1Parser
  private val int2 = parser("<<Int, Int>>")
  private val intToIntT = parser("Int -> Int")
  private val intToIntSetT = parser("Set(Int -> Int)")
  private val intT = parser("Int")
  private val intSetT = parser("Set(Int)")
  private val intSetSetT = parser("Set(Set(Int))")
  private val boolT = parser("Bool")
  private val intSeqT = parser("Seq(Int)")

  private def pair(i: Int, j: Int): TlaEx = tuple(int(i), int(j)).as(int2)

  test("decode bool") { rewriterType: SMTEncoding =>
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
    val eq = eql(decodedEx, originalEx).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode int") { rewriterType: SMTEncoding =>
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
    val eq = eql(decodedEx, originalEx).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode str") { rewriterType: SMTEncoding =>
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
    val eq = eql(decodedEx, originalEx).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode Int set") { rewriterType: SMTEncoding =>
    val originalEx = intSet().as(intSetT)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
  }

  test("decode Nat set") { rewriterType: SMTEncoding =>
    val originalEx = natSet().as(intSetT)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
  }

  test("decode set") { rewriterType: SMTEncoding =>
    val originalEx = enumSet(int(2), int(1), int(2)).as(intSetT)
    val simpleOriginalEx: TlaEx = enumSet(int(1), int(2)).as(intSetT)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(simpleOriginalEx == decodedEx)
    // hard core comparison
    val eq = eql(decodedEx.as(intSetT), simpleOriginalEx.as(intSetT)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode fun set") { rewriterType: SMTEncoding =>
    val domEx = enumSet(int(1), int(2)).as(intSetT)
    val cdmEx = enumSet(int(3), int(4)).as(intSetT)
    val originalEx = funSet(domEx, cdmEx).as(intToIntSetT)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
    // hard core comparison
    val eq = eql(decodedEx, originalEx).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode SUBSET S") { rewriterType: SMTEncoding =>
    val set = enumSet(int(1), int(2)).as(intSetT)
    val powset = powSet(set).as(intSetSetT)
    val state = new SymbState(powset, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(powset == decodedEx)
  }

  test("decode fun") { rewriterType: SMTEncoding =>
    val domEx = enumSet(int(1), int(2)).as(intSetT)
    val funEx =
      funDef(plus(name("x").as(intT), int(1)).as(intT), name("x").as(intT), domEx).as(intToIntT)
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)

    val expectedOutcome: TlaEx =
      apalacheSetAsFun(enumSet(pair(1, 2), pair(2, 3)).as(SetT1(int2))).as(intToIntT)
    assert(expectedOutcome == decodedEx)
  }

  // See https://github.com/informalsystems/apalache/issues/962
  test("decode fun does not show duplicate indices") { rewriterType: SMTEncoding =>
    // The specified domain includes duplicate values
    val domEx = enumSet(int(1), int(1)).as(intSetT)
    // But the expected domain after decoding should only include a single occurance
    val funEx = funDef(plus(name("x").as(intT), int(1)).as(intT), name("x").as(intT), domEx).as(intToIntT)
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    val expectedOutcome = apalacheSetAsFun(enumSet(tuple(int(1), int(2)).as(int2)).as(SetT1(int2))).as(intToIntT)
    assert(expectedOutcome == decodedEx)
  }

  test("decode statically empty fun") { rewriterType: SMTEncoding =>
    val domEx = enumSet().as(intSetT)
    val funEx = funDef(plus(name("x").as(intT), int(1)).as(intT), name("x").as(intT), domEx).as(intToIntT)
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    // the function of empty domain is simply SetAsFun({})
    val expectedOutcome = apalacheSetAsFun(enumSet().as(SetT1(int2))).as(intToIntT)
    assert(expectedOutcome == decodedEx)
    assertTlaExAndRestore(rewriter, nextState.setRex(eql(decodedEx, funEx).typed(BoolT1)))
  }

  test("decode dynamically empty fun") { rewriterType: SMTEncoding =>
    // this domain is not empty at the arena level, but it is in every SMT model
    def dynEmpty(left: BuilderEx): BuilderEx = {
      filter(name("t").as(intT), left, bool(false).as(boolT))
    }

    val domEx = dynEmpty(enumSet(int(1)).as(intSetT)).as(intSetT)
    // [ x \in {} |-> x + 1 ]
    val funEx =
      funDef(plus(name("x").as(intT), int(1)).as(intT), name("x").as(intT), domEx).as(intToIntT)
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    // the function of empty domain is simply SetAsFun({})
    val expectedOutcome = apalacheSetAsFun(enumSet().as(SetT1(int2))).as(intToIntT)
    assert(expectedOutcome == decodedEx)
    // we cannot directly compare the outcome, as it comes in the same form as a record
    assertTlaExAndRestore(rewriter, nextState.setRex(eql(decodedEx, funEx).typed(BoolT1)))
  }

  test("decode sequence") { rewriterType: SMTEncoding =>
    val seqEx =
      tuple(int(1), int(2), int(3), int(4)).as(intSeqT)
    val subseqEx = subseq(seqEx, int(2), int(3)).as(intSeqT)
    val state = new SymbState(subseqEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    val expected = tuple(int(2), int(3)).as(intSeqT)
    assert(decodedEx == expected)
  }

  test("decode tuple") { rewriterType: SMTEncoding =>
    val tupleEx: TlaEx =
      tuple(int(1), int(2), int(3)).as(parser("<<Int, Int, Int>>"))
    val state = new SymbState(tupleEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(tupleEx == decodedEx)
  }

  test("decode record") { rewriterType: SMTEncoding =>
    val recEx =
      enumFun(str("a"), int(1), str("b"), bool(true)).as(parser("[a: Int, b: Bool]"))
    val state = new SymbState(recEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(recEx == decodedEx)
  }

  test("decode row record") { rewriterType: SMTEncoding =>
    val recordT = parser("{ a: Int, b: Bool }")
    val recEx = enumFun(str("a"), int(1), str("b"), bool(true)).as(recordT)
    val state = new SymbState(recEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(recEx == decodedEx)
  }

  test("decode variant") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val vrt1 = variant("Foo", int(33)).as(variantT)
    val state = new SymbState(vrt1, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(vrt1 == decodedEx)
  }
}
