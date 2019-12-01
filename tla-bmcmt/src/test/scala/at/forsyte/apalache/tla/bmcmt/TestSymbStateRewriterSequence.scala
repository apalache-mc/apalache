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

  test("""SE-SEQ-APP: (<<>> <: Seq(Int))[1]""") {
    // regression: <<>>[1] should produce no contradiction, nor throw an exception
    val tuple = TlaFunOper.mkTuple()
    val annotatedTuple = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))

    val state = new SymbState(annotatedTuple, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
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

  test("""regression: Tail(<<>> <: Seq(Int)) does not unsat and its length is zero""") {
    val emptyTuple = TlaFunOper.mkTuple()
    val annotatedTuple = tla.withType(emptyTuple, AnnotationParser.toTla(SeqT(IntT())))
    val seqTail = tla.tail(annotatedTuple)

    val state = new SymbState(seqTail, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    // in this case, Tail may return an arbitrary value, but it should not get stuck!
    assert(solverContext.sat())
    // the length of the new sequence is 0, not -1
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(tla.int(0), tla.len(nextState.ex))))
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

  test("""regression: SE-SEQ-SUBSEQ: SubSeq(S, 3, 1) does not unsat and has length 0""") {
    val tuple = TlaFunOper.mkTuple(3.to(6) map tla.int :_*)
    val annotatedTuple = tla.withType(tuple, AnnotationParser.toTla(SeqT(IntT())))
    val subseqEx = tla.subseq(annotatedTuple, tla.int(3), tla.int(1))

    val state = new SymbState(subseqEx, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    // in this case, the solver should not be stuck by unsat, the value is simply arbitrary
    assert(solverContext.sat())
    // the length of the new sequence is 0, not -1
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(tla.int(0), tla.len(nextState.ex))))
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


  test("""SE-SEQ-EQ: <<4, 5>> = SubSeq(<<3, 4, 5, 6>>, 2, 3)""") {
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

  test("""SE-SEQ-DOMAIN: DOMAIN SubSeq(<<3, 4, 5, 6>>, 2, 3) = {2, 3}""") {
    val tuple3456 = TlaFunOper.mkTuple(3.to(6) map tla.int :_*)
    val annot3456 = tla.withType(tuple3456, AnnotationParser.toTla(SeqT(IntT())))
    val subseqEx = tla.subseq(annot3456, tla.int(2), tla.int(3))
    val domEx = tla.dom(subseqEx)

    val state = new SymbState(domEx, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter,
      nextState.setRex(tla.eql(tla.enumSet(tla.int(2), tla.int(3)), nextState.ex)))
  }

  test("""SEQ-CONCAT: <<9, 10>> \o SubSeq(S, 2, 3)""") {
    val tuple3_6 = TlaFunOper.mkTuple(3.to(6) map tla.int :_*)
    val seqT = AnnotationParser.toTla(SeqT(IntT()))
    val annotatedTuple = tla.withType(tuple3_6, seqT)
    val subseq = tla.subseq(annotatedTuple, tla.int(2), tla.int(3)) // <<4, 5>>
    val tuple9_10 = tla.withType(TlaFunOper.mkTuple(tla.int(9), tla.int(10)), seqT)
    val concat = tla.concat(tuple9_10, subseq)

    val state = new SymbState(concat, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(SeqT(IntT()) == result.cellType)

    val expected = tla.withType(TlaFunOper.mkTuple(tla.int(9), tla.int(10), tla.int(4), tla.int(5)), seqT)

    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(expected, nextState.ex)))
  }

  test("""regression: SEQ-CONCAT: <<9, 10>> \o Tail(<<>>) does not unsat""") {
    val seqT = AnnotationParser.toTla(SeqT(IntT()))
    val empty = tla.withType(TlaFunOper.mkTuple(), seqT)
    val tuple9_10 = tla.withType(TlaFunOper.mkTuple(tla.int(9), tla.int(10)), seqT)
    // Tail(<<>>) produces some undefined value. In this case, \o should also produce an undefined value.
    val concat = tla.concat(tuple9_10, tla.tail(empty))

    val state = new SymbState(concat, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    // the result is undefined, but it should be sat
    assert(solverContext.sat())
  }

  // for PICK see TestCherryPick

  // TODO: except
}
