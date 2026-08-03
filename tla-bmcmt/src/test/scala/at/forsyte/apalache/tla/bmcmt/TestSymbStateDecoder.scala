package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.config.SMTEncoding
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.{tla, BuilderT}

trait TestSymbStateDecoder extends RewriterBase {
  private val parser = DefaultType1Parser
  private val int2 = parser("<<Int, Int>>")

  private def pair(i: Int, j: Int): BuilderT = tla.tuple(tla.int(i), tla.int(j))

  test("decode bool") { rewriterType: SMTEncoding =>
    val originalEx: BuilderT = tla.bool(true)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(originalEx, decodedEx)
    // hard core comparison
    val eq = tla.eql(tla.unchecked(decodedEx), originalEx)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode int") { rewriterType: SMTEncoding =>
    val originalEx = tla.int(3)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(originalEx, decodedEx)
    // hard core comparison
    val eq = tla.eql(tla.unchecked(decodedEx), originalEx)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode str") { rewriterType: SMTEncoding =>
    val originalEx: BuilderT = tla.str("hello")
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(originalEx, decodedEx)
    // hard core comparison
    val eq = tla.eql(tla.unchecked(decodedEx), originalEx)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode Int set") { rewriterType: SMTEncoding =>
    val originalEx = tla.intSet()
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(originalEx, decodedEx)
  }

  test("decode Nat set") { rewriterType: SMTEncoding =>
    val originalEx = tla.natSet()
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(originalEx, decodedEx)
  }

  test("decode set") { rewriterType: SMTEncoding =>
    val originalEx = tla.enumSet(tla.int(2), tla.int(1), tla.int(2))
    val simpleOriginalEx = tla.enumSet(tla.int(1), tla.int(2))
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(simpleOriginalEx, decodedEx)
    // hard core comparison
    val eq = tla.eql(tla.unchecked(decodedEx), simpleOriginalEx)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode fun set") { rewriterType: SMTEncoding =>
    val domEx = tla.enumSet(tla.int(1), tla.int(2))
    val cdmEx = tla.enumSet(tla.int(3), tla.int(4))
    val originalEx = tla.funSet(domEx, cdmEx)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(originalEx, decodedEx)
    // hard core comparison
    val eq = tla.eql(tla.unchecked(decodedEx), originalEx)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("decode SUBSET S") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val powset = tla.powSet(set)
    val state = new SymbState(powset, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(powset, decodedEx)
  }

  test("decode fun") { rewriterType: SMTEncoding =>
    val domEx = tla.enumSet(tla.int(1), tla.int(2))
    val funEx =
      tla.funDef(tla.plus(tla.name("x", IntT1), tla.int(1)), (tla.name("x", IntT1), domEx))
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)

    val expectedOutcome: BuilderT = tla.setAsFun(tla.enumSet(pair(1, 2), pair(2, 3)))
    assertBuildEqual(expectedOutcome, decodedEx)
  }

  // See https://github.com/apalache-mc/apalache/issues/962
  test("decode fun does not show duplicate indices") { rewriterType: SMTEncoding =>
    // The specified domain includes duplicate values
    val domEx = tla.enumSet(tla.int(1), tla.int(1))
    // But the expected domain after decoding should only include a single occurance
    val funEx = tla.funDef(tla.plus(tla.name("x", IntT1), tla.int(1)), (tla.name("x", IntT1), domEx))
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    val expectedOutcome = tla.setAsFun(tla.enumSet(tla.tuple(tla.int(1), tla.int(2))))
    assertBuildEqual(expectedOutcome, decodedEx)
  }

  test("decode statically empty fun") { rewriterType: SMTEncoding =>
    val domEx = tla.emptySet(IntT1)
    val funEx = tla.funDef(tla.plus(tla.name("x", IntT1), tla.int(1)), (tla.name("x", IntT1), domEx))
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    // the function of empty domain is simply SetAsFun({})
    val expectedOutcome = tla.setAsFun(tla.emptySet(int2))
    assertBuildEqual(expectedOutcome, decodedEx)
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(tla.unchecked(decodedEx), funEx)))
  }

  test("decode dynamically empty fun") { rewriterType: SMTEncoding =>
    // this domain is not empty at the arena level, but it is in every SMT model
    def dynEmpty(left: BuilderT): BuilderT =
      tla.filter(tla.name("t", IntT1), left, tla.bool(false))

    val domEx = dynEmpty(tla.enumSet(tla.int(1)))
    // [ x \in {} |-> x + 1 ]
    val funEx =
      tla.funDef(tla.plus(tla.name("x", IntT1), tla.int(1)), (tla.name("x", IntT1), domEx))
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    // the function of empty domain is simply SetAsFun({})
    val expectedOutcome = tla.setAsFun(tla.emptySet(int2))
    assertBuildEqual(expectedOutcome, decodedEx)
    // we cannot directly compare the outcome, as it comes in the same form as a record
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(tla.unchecked(decodedEx), funEx)))
  }

  test("decode sequence") { rewriterType: SMTEncoding =>
    val seqEx = tla.seq(tla.int(1), tla.int(2), tla.int(3), tla.int(4))
    val subseqEx = tla.subseq(seqEx, tla.int(2), tla.int(3))
    val state = new SymbState(subseqEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    val expected = tla.seq(tla.int(2), tla.int(3))
    assertBuildEqual(expected, decodedEx)
  }

  test("decode tuple") { rewriterType: SMTEncoding =>
    val tupleEx = tla.tuple(tla.int(1), tla.int(2), tla.int(3))
    val state = new SymbState(tupleEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(tupleEx, decodedEx)
  }

  test("decode record") { rewriterType: SMTEncoding =>
    val recEx = tla.rec(
        "a" -> tla.int(1),
        "b" -> tla.bool(true),
    )
    val state = new SymbState(recEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(recEx, decodedEx)
  }

  test("decode row record") { rewriterType: SMTEncoding =>
    val recEx = tla
      .rec(
          "a" -> tla.int(1),
          "b" -> tla.bool(true),
      )
      .map(_.withTag(Typed(parser("{ a: Int, b: Bool }"))))
    val state = new SymbState(recEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(recEx, decodedEx)
  }

  test("decode variant") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val vrt1 = tla.variant("Foo", tla.int(33), variantT.asInstanceOf[VariantT1])
    val state = new SymbState(vrt1, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assertBuildEqual(vrt1, decodedEx)
  }

  test("decode gen: Regression #1 for #2702") { rewriterType: SMTEncoding =>
    val valName = tla.name("gen", SetT1(IntT1))
    val genEx = tla.gen(tla.int(1), SetT1(IntT1))
    val x = tla.name("x", IntT1)
    val cond = tla.forall(x, valName, tla.eql(x, tla.int(0)))

    val ex = tla.and(tla.eql(valName, genEx), cond)

    val arenaWithGenCell = arena.appendCell(SetT1(IntT1))
    val genCell = arenaWithGenCell.topCell

    val rewriter = create(rewriterType)
    val state = new SymbState(ex, arenaWithGenCell, Binding("gen" -> genCell))
    val rewrittenState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())

    val decoder = new SymbStateDecoder(solverContext, rewriter)

    val decodedVal: TlaEx = decoder.decodeCellToTlaEx(rewrittenState.arena, genCell)

    assert(
        decodedVal match {
          case OperEx(TlaSetOper.enumSet, args @ _*) =>
            args.forall { _ == tla.int(0).build }
          case _ => false
        }
    )
  }

  test("decode gen: Regression #2 for #2702") { rewriterType: SMTEncoding =>
    val valName = tla.name("gen", SetT1(IntT1))
    val genEx = tla.gen(tla.int(1), SetT1(IntT1))
    val x = tla.name("x", IntT1)
    val cond = tla.forall(x, valName, tla.neql(x, tla.int(42)))

    val ex = tla.and(tla.eql(valName, genEx), cond)

    val arenaWithGenCell = arena.appendCell(SetT1(IntT1))
    val genCell = arenaWithGenCell.topCell

    val rewriter = create(rewriterType)
    val state = new SymbState(ex, arenaWithGenCell, Binding("gen" -> genCell))
    val rewrittenState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())

    val decoder = new SymbStateDecoder(solverContext, rewriter)

    val decodedVal: TlaEx = decoder.decodeCellToTlaEx(rewrittenState.arena, genCell)

    assert(
        decodedVal match {
          case OperEx(TlaSetOper.enumSet, args @ _*) => !args.contains(tla.int(42).build)
          case _                                     => false
        }
    )
  }

}
