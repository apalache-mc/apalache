package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.rules.aux.ProtoSeqOps
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.ApalacheInternalOper

trait TestSymbStateRewriterSequence extends RewriterBase {
  private val intT = IntT1
  private val boolT = BoolT1
  private val intSetT = SetT1(IntT1)
  private val intSeqT = SeqT1(IntT1)

  // As sequences are not distinguishable from tuples, we need a type annotation.
  // In the not so far away future, a type inference engine would tell us, whether to construct a sequence or a tuple
  test("""<<>> as Seq(Int)""") { rewriterType: SMTEncoding =>
    val tup = tuple().as(intSeqT)

    val state = new SymbState(tup, arena, Binding())
    val nextState = create(rewriterType).rewriteUntilDone(state)
    assert(solverContext.sat())
    nextState.ex match {
      case NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        assert(CellTFrom(SeqT1(IntT1)) == cell.cellType)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""<<3, 4, 5>> as Seq(Int)""") { rewriterType: SMTEncoding =>
    val tup = tuple(3.to(5).map(int): _*).as(intSeqT)

    val state = new SymbState(tup, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    nextState.ex match {
      case NameEx(name) =>
        assert(solverContext.sat())
        val cell = nextState.arena.findCellByName(name)
        assert(CellTFrom(SeqT1(IntT1)) == cell.cellType)
        // test that the proto sequence is correct
        val protoSeqOps = new ProtoSeqOps(rewriter)
        val (protoSeq, len, capacity) = protoSeqOps.unpackSeq(nextState.arena, cell)
        assert(capacity == 3)
        // compare the length
        assertTlaExAndRestore(rewriter, nextState.setRex(eql(len.toNameEx, int(3)).as(BoolT1)))

        // compare the elements
        def cmp(indexBase1: Int, expectedValue: Int): TlaEx =
          eql(protoSeqOps.at(nextState.arena, protoSeq, indexBase1).toNameEx, int(expectedValue)).as(BoolT1)

        assertTlaExAndRestore(rewriter, nextState.setRex(cmp(1, 3)))
        assertTlaExAndRestore(rewriter, nextState.setRex(cmp(2, 4)))
        assertTlaExAndRestore(rewriter, nextState.setRex(cmp(3, 5)))

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""(<<3, 4, 5>> as Seq(Int))[2]""") { rewriterType: SMTEncoding =>
    val tup = tuple(3.to(5).map(int): _*).as(intSeqT)

    val state = new SymbState(tup, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val seq = nextState.asCell
    val eq1 = eql(appFun(seq.toNameEx.as(intSeqT), int(1)).as(intT), int(3)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = eql(appFun(seq.toNameEx.as(intSeqT), int(2)).as(intT), int(4)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = eql(appFun(seq.toNameEx.as(intSeqT), int(3)).as(intT), int(5)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
  }

  test("""(<<>> as Seq(Int))[1]""") { rewriterType: SMTEncoding =>
    // regression: <<>>[i] should produce no contradiction, nor throw an exception
    val tup = tuple().as(intSeqT)
    val app = appFun(tup, int(1)).as(IntT1)

    val state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    val _ = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""(<<>> as Seq(Int))[x] when x = 1""") { rewriterType: SMTEncoding =>
    // regression: <<>>[i] should produce no contradiction, nor throw an exception
    val tup = tuple().as(intSeqT)
    val app = appFun(tup, name("x").as(IntT1)).as(IntT1)

    var state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    // rewrite 1 into a cell, so function application does not statically detect out of bounds
    state = rewriter.rewriteUntilDone(state.setRex(int(1).as(IntT1)))
    state = state.setBinding(Binding("x" -> state.asCell))
    val _ = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""(<<1, 2>> as Seq(Int))[7]""") { rewriterType: SMTEncoding =>
    // regression: <<1, 2>>[i] for i = 7 should produce no contradiction, nor throw an exception
    val tup = tuple(int(1), int(2)).as(intSeqT)
    val app = appFun(tup, int(7)).as(IntT1)

    val state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    val _ = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""(<<1, 2>> as Seq(Int))[x] for x = 7""") { rewriterType: SMTEncoding =>
    // regression: <<1, 2>>[i] for i = 7 should produce no contradiction, nor throw an exception
    val tup = tuple(int(1), int(2)).as(intSeqT)
    val app = appFun(tup, name("x").as(IntT1)).as(IntT1)

    var state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    // rewrite 7 into a cell, so function application does not statically detect out of bounds
    state = rewriter.rewriteUntilDone(state.setRex(int(7).as(IntT1)))
    state = state.setBinding(Binding("x" -> state.asCell))
    val _ = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""Head(<<3, 4, 5>> as Seq(Int))""") { rewriterType: SMTEncoding =>
    val tup = tuple(3.to(5).map(int): _*).as(intSeqT)
    val seqHead = head(tup).as(intT)
    val eq = eql(seqHead, int(3)).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Len(<<3, 4, 5>> <: Seq(Int))""") { rewriterType: SMTEncoding =>
    val tup = tuple(3.to(5).map(i => int(i)): _*).as(intSeqT)
    val seqLen = len(tup).as(intT)
    val eq = eql(seqLen, int(3)).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Tail(<<3, 4, 5>> as Seq(Int))""") { rewriterType: SMTEncoding =>
    val tup = tuple(3.to(5).map(int): _*).as(intSeqT)
    val seqTail = tail(tup).as(intSeqT)
    val expected = tuple(int(4), int(5)).as(intSeqT)
    val eq = eql(seqTail, expected).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Tail(<<>> as Seq(Int)) throws an error""") { rewriterType: SMTEncoding =>
    // Tail(<<>>) returns <<>>. Since Tail(<<>>) is undefined, it is a correct behavior.
    val emptyTuple = tuple().as(intSeqT)
    val seqTail = tail(emptyTuple).as(intSeqT)
    val eq = eql(len(seqTail).as(intT), int(0)).as(boolT)
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""regression: Tail(SubSeq(<<1>>, 1, 0)) does not unsat and its length is -1""") { rewriterType: SMTEncoding =>
    val tuple1 = tuple(int(1)).as(intSeqT)
    val seqTail = tail(subseq(tuple1, int(1), int(0)).as(intSeqT)).as(intSeqT)
    // One can argue that the Len(Tail(seqTail)) should be 0,
    // but Tail is undefined on empty sequences, so we are free to report -1.
    val eq = eql(len(seqTail).as(intT), int(-1)).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<3, 4, 5, 6>>, 2, 3)""") { rewriterType: SMTEncoding =>
    val tup = tuple(3.to(6).map(int): _*).as(intSeqT)
    val subseqEx = subseq(tup, int(2), int(3)).as(intSeqT)

    val state = new SymbState(subseqEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(CellTFrom(SeqT1(IntT1)) == result.cellType)
    val eq1 = eql(appFun(result.toNameEx.as(intSeqT), int(1)).as(intT), int(4)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = eql(appFun(result.toNameEx.as(intSeqT), int(2)).as(intT), int(5)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = eql(len(result.toNameEx.as(intSeqT)).as(intT), int(2)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
  }

  test("""regression: SubSeq(<<3, 4, 5, 6>>, 3, 1) does not unsat and has length 0""") { rewriterType: SMTEncoding =>
    val tup = tuple(3.to(6).map(int): _*).as(intSeqT)
    val subseqEx = subseq(tup, int(3), int(1)).as(intSeqT)
    val eq = eql(len(subseqEx).as(intT), int(0)).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<3, 4, 5, 6>>, 5, 6) does not unsat and has length 0""") { rewriterType: SMTEncoding =>
    val tup = tuple(3.to(6).map(int): _*).as(intSeqT)
    val subseqEx = subseq(tup, int(5), int(6)).as(intSeqT)
    val eq = eql(len(subseqEx).as(intT), int(0)).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<3, 4, 5, 6>>, 1, 10) = <<3, 4, 5, 6>>""") { rewriterType: SMTEncoding =>
    val tup = tuple(3.to(6).map(int): _*).as(intSeqT)
    val subseqEx = subseq(tup, int(1), int(10)).as(intSeqT)
    val eq = eql(subseqEx, tup).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<3, 4, 5, 6>>, 0, 4) = <<3, 4, 5, 6>>""") { rewriterType: SMTEncoding =>
    // TLC throws an error in this case. We cannot produce side effects, so we are doing the best we can do here.
    val tup = tuple(3.to(6).map(int): _*).as(intSeqT)
    val subseqEx = subseq(tup, int(0), int(10)).as(intSeqT)
    val eq = eql(subseqEx, tup).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<3, 4, 5, 6>>, 1, 0) = <<>>""") { rewriterType: SMTEncoding =>
    // TLC throws an error in this case. We cannot produce side effects, so we are doing the best we can do here.
    val tup = tuple(3.to(6).map(int): _*).as(intSeqT)
    val subseqEx = subseq(tup, int(1), int(0)).as(intSeqT)
    val eq = eql(subseqEx, tuple().as(intSeqT)).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<1, 2, 3>>, 1, 2) = SubSeq(<<1, 2, 4>>, 1, 2)""") { rewriterType: SMTEncoding =>
    val seq123 = tuple(int(1), int(2), int(3)).as(SeqT1(IntT1))
    val subseqEx1 = subseq(seq123, int(1), int(2)).as(intSeqT)
    val seq124 = tuple(int(1), int(2), int(4)).as(SeqT1(IntT1))
    val subseqEx2 = subseq(seq124, int(1), int(2)).as(intSeqT)
    val eq = eql(subseqEx1, subseqEx2).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<1, 2, 3>>, 1, 3) /= SubSeq(<<1, 2, 4>>, 1, 3)""") { rewriterType: SMTEncoding =>
    val seq123 = tuple(int(1), int(2), int(3)).as(SeqT1(IntT1))
    val seq124 = tuple(int(1), int(2), int(4)).as(SeqT1(IntT1))
    val subseqEx1 = subseq(seq123, int(1), int(3)).as(intSeqT)
    val subseqEx2 = subseq(seq124, int(1), int(3)).as(intSeqT)
    val eq = eql(subseqEx1, subseqEx2).as(boolT)
    val neq = not(eq).as(BoolT1)

    val state = new SymbState(neq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Append(<<4, 5>>, 10)""") { rewriterType: SMTEncoding =>
    val tup = tuple(4.to(5).map(int): _*).as(intSeqT)
    val seqAppend = append(tup, int(10)).as(intSeqT)

    val state = new SymbState(seqAppend, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(CellTFrom(SeqT1(IntT1)) == result.cellType)
    val eq1 = eql(appFun(result.toNameEx.as(intSeqT), int(1)).as(intT), int(4)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = eql(appFun(result.toNameEx.as(intSeqT), int(2)).as(intT), int(5)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = eql(appFun(result.toNameEx.as(intSeqT), int(3)).as(intT), int(10)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
    val eq4 = eql(len(result.toNameEx.as(intSeqT)).as(intT), int(3)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq4))
  }

  test("""Append(SubSeq(S, 2, 3), 10)""") { rewriterType: SMTEncoding =>
    val tup = tuple(3.to(6).map(int): _*).as(intSeqT)
    val subseqEx = subseq(tup, int(2), int(3)).as(intSeqT)
    val seqAppend = append(subseqEx, int(10)).as(intSeqT)

    val state = new SymbState(seqAppend, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(CellTFrom(SeqT1(IntT1)) == result.cellType)
    val eq1 = eql(appFun(result.toNameEx.as(intSeqT), int(1)).as(intT), int(4)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = eql(appFun(result.toNameEx.as(intSeqT), int(2)).as(intT), int(5)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = eql(appFun(result.toNameEx.as(intSeqT), int(3)).as(intT), int(10)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
    val eq4 = eql(len(result.toNameEx.as(intSeqT)).as(intT), int(3)).as(boolT)
    assertTlaExAndRestore(rewriter, nextState.setRex(eq4))
  }

  test("""<<4, 5>> = SubSeq(<<3, 4, 5, 6>>, 2, 3)""") { rewriterType: SMTEncoding =>
    val tup3456 = tuple(3.to(6).map(int): _*).as(intSeqT)
    val subseqEx = subseq(tup3456, int(2), int(3)).as(intSeqT)
    val tup45 = tuple(4.to(5).map(int): _*).as(intSeqT)
    val eq = eql(tup45, subseqEx).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""DOMAIN SubSeq(<<3, 4, 5, 6>>, 2, 3) equals {1, 2}""") { rewriterType: SMTEncoding =>
    val tup3456 = tuple(3.to(6).map(int): _*).as(intSeqT)
    val subseqEx = subseq(tup3456, int(2), int(3)).as(intSeqT)
    val domEx = dom(subseqEx).as(intSetT)
    val eq = eql(domEx, enumSet(int(1), int(2)).as(intSetT)).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""<<9, 10>> \o SubSeq(<<3, 4, 5, 6>>, 2, 3)""") { rewriterType: SMTEncoding =>
    val tup3_6 = tuple(3.to(6).map(int): _*).as(intSeqT)
    val subseqRes = subseq(tup3_6, int(2), int(3)).as(intSeqT) // <<4, 5>>
    val tup9_10 = tuple(int(9), int(10)).as(intSeqT)
    val concatRes = concat(tup9_10, subseqRes).as(intSeqT)
    val expected = tuple(int(9), int(10), int(4), int(5)).as(intSeqT)
    val eq = eql(concatRes, expected).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""regression: <<9, 10>> \o Tail(<<>>) does not unsat""") { rewriterType: SMTEncoding =>
    val t9_10 = tuple(int(9), int(10)).as(intSeqT)
    val t1 = tuple(int(1)).as(intSeqT)
    // Tail(SubSeq(<<1>>, 1, 0)) produces some undefined value. In this case, \o should also produce an undefined value.
    val concatRes = concat(t9_10, tail(subseq(t1, int(1), int(0)).as(intSeqT)).as(intSeqT)).as(intSeqT)

    val state = new SymbState(concatRes, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteUntilDone(state)
    // the result is undefined, but it should be sat
    assert(solverContext.sat())
  }

  test("""(<<3, 4, 5, 6>> EXCEPT ![2] = 7) = <<3, 7, 5, 6>>""") { rewriterType: SMTEncoding =>
    val tup3to6 = tuple(3.to(6).map(int): _*).as(intSeqT)
    val tup3756 = tuple(Seq(3, 7, 5, 6).map(int): _*).as(intSeqT)
    val exceptEx = except(tup3to6, tuple(int(2)).as(TupT1(IntT1)), int(7)).as(intSeqT)
    val eq = eql(exceptEx, tup3756).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""(<<3, 4, 5, 6>> EXCEPT ![10] = 7) = <<3, 4, 5, 6>>""") { rewriterType: SMTEncoding =>
    val tup3to6 = tuple(3.to(6).map(int): _*).as(intSeqT)
    val exceptEx = except(tup3to6, tuple(int(10)).as(TupT1(IntT1)), int(7)).as(intSeqT)
    // since 10 does not belong to the domain, the sequence does not change
    val eq = eql(exceptEx, tup3to6).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""(<< >> EXCEPT ![10] = 7) = << >>""") { rewriterType: SMTEncoding =>
    val emptyTuple = tuple().as(intSeqT)
    val exceptEx = except(emptyTuple, tuple(int(10)).as(TupT1(IntT1)), int(7)).as(intSeqT)
    // since 10 does not belong to the domain, the sequence does not change
    val eq = eql(exceptEx, emptyTuple).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""(ApalacheSeqCapacity(<<3, 4, 5, 6>>) = 4""") { rewriterType: SMTEncoding =>
    val seq3to6 = tuple(3.to(6).map(int): _*).as(intSeqT)
    val ex = OperEx(ApalacheInternalOper.apalacheSeqCapacity, seq3to6)(Typed(IntT1))
    val eq = eql(ex, int(4)).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  // for PICK see TestCherryPick
}
