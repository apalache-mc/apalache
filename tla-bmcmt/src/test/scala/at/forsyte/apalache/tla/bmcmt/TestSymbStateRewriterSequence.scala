package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterSequence extends RewriterBase {
  // As sequences are not distinguishable from tuples, we need a type annotation.
  // In the not so far away future, a type inference engine would tell us, whether to construct a sequence or a tuple
  test("""SE-SEQ-CTOR: <<>> <: Seq(Int)""") {
    val tuple = TlaFunOper.mkTuple()
    val annotatedTuple = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))

    val state = new SymbState(annotatedTuple, CellTheory(), arena, new Binding)
    val nextState = create().rewriteUntilDone(state)
    assert(solverContext.sat())
    nextState.ex match {
      case NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        assert(SeqT(IntT()) == cell.cellType)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SEQ-CTOR: <<1, 2, 3>> <: Seq(Int)""") {
    val tuple = TlaFunOper.mkTuple(1.to(3) map tla.int :_*)
    val annotatedTuple = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))

    val state = new SymbState(annotatedTuple, CellTheory(), arena, new Binding)
    val nextState = create().rewriteUntilDone(state)
    assert(solverContext.sat())
    nextState.ex match {
      case NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        assert(SeqT(IntT()) == cell.cellType)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SEQ-APP: (<<3, 4, 5>> <: Seq(Int))[2]""") {
    val tuple = TlaFunOper.mkTuple(3.to(5) map tla.int :_*)
    val annotatedTuple = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))

    val state = new SymbState(annotatedTuple, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val seq = nextState.asCell
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(seq.toNameEx, tla.int(1)), tla.int(3))))
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(seq.toNameEx, tla.int(2)), tla.int(4))))
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(seq.toNameEx, tla.int(3)), tla.int(5))))
  }

  test("""SE-SEQ-HEAD: Head(<<3, 4, 5>> <: Seq(Int))""") {
    val tuple = TlaFunOper.mkTuple(3.to(5) map tla.int :_*)
    val annotatedTuple = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))
    val seqApp = tla.head(annotatedTuple)

    val state = new SymbState(seqApp, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(IntT() == result.cellType)
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(result.toNameEx, tla.int(3))))
  }

  test("""SE-SEQ-LEN: Len(<<3, 4, 5>> <: Seq(Int))""") {
    val tuple = TlaFunOper.mkTuple(3.to(5) map tla.int :_*)
    val annotatedTuple = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))
    val seqApp = tla.len(annotatedTuple)

    val state = new SymbState(seqApp, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(IntT() == result.cellType)
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(result.toNameEx, tla.int(3))))
  }

  test("""SE-SEQ-TAIL: Tail(<<3, 4, 5>> <: Seq(Int))""") {
    val tuple = TlaFunOper.mkTuple(3.to(5) map tla.int :_*)
    val annotatedTuple = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))
    val seqTail = tla.tail(annotatedTuple)

    val state = new SymbState(seqTail, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(SeqT(IntT()) == result.cellType)
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(result.toNameEx, tla.int(1)), tla.int(4))))
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(result.toNameEx, tla.int(2)), tla.int(5))))
  }

  test("""SE-SEQ-SUBSEQ: SubSeq(S, 2, 4)""") {
    val tuple = TlaFunOper.mkTuple(3.to(6) map tla.int :_*)
    val annotatedTuple = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))
    val subseqEx = tla.subseq(annotatedTuple, tla.int(2), tla.int(3))

    val state = new SymbState(subseqEx, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(SeqT(IntT()) == result.cellType)
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(result.toNameEx, tla.int(1)), tla.int(4))))
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(result.toNameEx, tla.int(2)), tla.int(5))))
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.len(result.toNameEx), tla.int(2))))
  }

  test("""SE-SEQ-APPEND: Append(S, 10)""") {
    val tuple = TlaFunOper.mkTuple(4.to(5) map tla.int :_*)
    val annotatedTuple = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))
    val append = tla.append(annotatedTuple, tla.int(10))

    val state = new SymbState(append, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(SeqT(IntT()) == result.cellType)
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(result.toNameEx, tla.int(1)), tla.int(4))))
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(result.toNameEx, tla.int(2)), tla.int(5))))
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(result.toNameEx, tla.int(3)), tla.int(10))))
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.len(result.toNameEx), tla.int(3))))
  }

  test("""SE-SEQ-APPEND: Append(SubSeq(S, 2, 3), 10)""") {
    val tuple = TlaFunOper.mkTuple(3.to(6) map tla.int :_*)
    val annotatedTuple = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))
    val subseqEx = tla.subseq(annotatedTuple, tla.int(2), tla.int(3))
    val append = tla.append(subseqEx, tla.int(10))

    val state = new SymbState(append, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(SeqT(IntT()) == result.cellType)
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(result.toNameEx, tla.int(1)), tla.int(4))))
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(result.toNameEx, tla.int(2)), tla.int(5))))
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.appFun(result.toNameEx, tla.int(3)), tla.int(10))))
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.len(result.toNameEx), tla.int(3))))
  }


  test("""SE-SEQ-EQ: <<4, 5>> = SubSeq(<<3, 4, 5, 6>>, 2, 4)""") {
    val tuple3456 = TlaFunOper.mkTuple(3.to(6) map tla.int :_*)
    val annot3456 = tla.withType(tuple3456, AnnotationParser.toTla(SeqT(IntT())))
    val subseqEx = tla.subseq(annot3456, tla.int(2), tla.int(3))
    val tuple45 = TlaFunOper.mkTuple(4.to(5) map tla.int :_*)
    val annot45 = tla.withType(tuple45, AnnotationParser.toTla(SeqT(IntT())))
    val eq = tla.eql(annot45, subseqEx)

    val state = new SymbState(eq, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(BoolT() == result.cellType)
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.bool(true), nextState.ex)))
  }

  // TODO: pick
  // TODO: append
  // TODO: concat \o
}
