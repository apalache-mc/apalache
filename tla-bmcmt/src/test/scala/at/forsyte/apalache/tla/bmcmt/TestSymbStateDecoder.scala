package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{AnnotationParser, FinSetT, IntT, SeqT}
import at.forsyte.apalache.tla.lir.{TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.values.{TlaIntSet, TlaNatSet}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateDecoder extends RewriterBase {
  test("decode bool") {
    val originalEx = tla.bool(true)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
    // hard core comparison
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(decodedEx, originalEx)))
  }

  test("decode int") {
    val originalEx = tla.int(3)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
    // hard core comparison
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(decodedEx, originalEx)))
  }

  test("decode str") {
    val originalEx = tla.str("hello")
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
    // hard core comparison
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(decodedEx, originalEx)))
  }

  test("decode Int set") {
    val originalEx = ValEx(TlaIntSet)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
  }

  test("decode Nat set") {
    val originalEx = ValEx(TlaNatSet)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
  }

  test("decode set") {
    val originalEx = tla.enumSet(tla.int(2), tla.int(1), tla.int(2))
    val simpleOriginalEx = tla.enumSet(tla.int(1), tla.int(2))
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(simpleOriginalEx == decodedEx)
    // hard core comparison
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(decodedEx, simpleOriginalEx)))
  }

  test("decode fun set") {
    val domEx = tla.enumSet(tla.int(1), tla.int(2))
    val cdmEx = tla.enumSet(tla.int(3), tla.int(4))
    val originalEx = tla.funSet(domEx, cdmEx)
    val state = new SymbState(originalEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(originalEx == decodedEx)
    // hard core comparison
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(decodedEx, originalEx)))
  }

  test("decode SUBSET S") {
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val powset = tla.powSet(set)
    val state = new SymbState(powset, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(powset == decodedEx)
  }

  test("decode fun") {
    val domEx = tla.enumSet(tla.int(1), tla.int(2))
    val funEx = tla.funDef(tla.plus(tla.name("x"), tla.int(1)), tla.name("x"), domEx)
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    val expectedOutcome =
      tla.atat(tla.int(1), tla.int(2), tla.int(2), tla.int(3))
    assert(expectedOutcome == decodedEx)
    // we cannot directly compare the outcome, as it comes in the same form as a record
    //    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(decodedEx, funEx)))
  }

  test("decode statically empty fun") {
    val domEx = tla.withType(tla.enumSet(), AnnotationParser.toTla(FinSetT(IntT())))
    val funEx = tla.funDef(tla.plus(tla.name("x"), tla.int(1)), tla.name("x"), domEx)
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    // this is the standard outcome for an empty-domain function: {x \in {} |-> {}}
    val expectedOutcome = tla.atat()
    assert(expectedOutcome == decodedEx)
    // we cannot directly compare the outcome, as it comes in the same form as a record
    //    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(decodedEx, funEx)))
  }

  test("decode dynamically empty fun") {
    // this domain is not empty at the arena level, but it is in every SMT model
    def dynEmpty(left: TlaEx): TlaEx = {
      tla.filter(tla.name("t"), left, tla.bool(false))
    }

    val domEx = dynEmpty(tla.enumSet(tla.int(1)))
    val funEx = tla.funDef(tla.plus(tla.name("x"), tla.int(1)), tla.name("x"), domEx)
    val state = new SymbState(funEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    // this is the standard outcome for an empty-domain function: {x \in {} |-> {}}
    val expectedOutcome = tla.atat()
    assert(expectedOutcome == decodedEx)
    // we cannot directly compare the outcome, as it comes in the same form as a record
    //    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(decodedEx, funEx)))
  }

  test("decode sequence") {
    val seqEx =
      tla.withType(tla.tuple(tla.int(1), tla.int(2), tla.int(3), tla.int(4)), AnnotationParser.toTla(SeqT(IntT())))
    val subseqEx = tla.subseq(seqEx, tla.int(2), tla.int(3))
    val state = new SymbState(subseqEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(tla.tuple(tla.int(2), tla.int(3)) == decodedEx)
  }

  test("decode tuple") {
    val tupleEx =
      tla.tuple(tla.int(1), tla.int(2), tla.int(3))
    val state = new SymbState(tupleEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(tupleEx == decodedEx)
  }

  test("decode record") {
    val recEx =
      tla.enumFun(tla.str("a"), tla.int(1), tla.str("b"), tla.bool(true))
    val state = new SymbState(recEx, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val cell = nextState.asCell
    val decoder = new SymbStateDecoder(solverContext, rewriter)
    val decodedEx = decoder.decodeCellToTlaEx(nextState.arena, cell)
    assert(recEx == decodedEx)
  }
}
