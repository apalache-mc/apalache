package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.rules.aux.ProtoSeqOps
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.ApalacheInternalOper
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterSequence extends RewriterBase {
  private def intSeq(values: Int*): TBuilderInstruction =
    if (values.isEmpty) tla.emptySeq(IntT1) else tla.seq(values.map(i => tla.int(i)): _*)

  private def seqCell(cell: ArenaCell): TBuilderInstruction =
    tla.unchecked(cell.toNameEx)

  private def intSeqAt(seq: TBuilderInstruction, index: Int): TBuilderInstruction =
    tla.app(seq, tla.int(index))

  // As sequences are not distinguishable from tuples, we need a type annotation.
  // In the not so far away future, a type inference engine would tell us, whether to construct a sequence or a tuple
  test("""<<>> as Seq(Int)""") { rewriterType: SMTEncoding =>
    val tup = intSeq()

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
    val tup = intSeq(3.to(5): _*)

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
        assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(tla.unchecked(len.toNameEx), tla.int(3))))

        // compare the elements
        def cmp(indexBase1: Int, expectedValue: Int): TBuilderInstruction =
          tla.eql(tla.unchecked(protoSeqOps.at(nextState.arena, protoSeq, indexBase1).toNameEx), tla.int(expectedValue))

        assertTlaExAndRestore(rewriter, nextState.setRex(cmp(1, 3)))
        assertTlaExAndRestore(rewriter, nextState.setRex(cmp(2, 4)))
        assertTlaExAndRestore(rewriter, nextState.setRex(cmp(3, 5)))

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""(<<3, 4, 5>> as Seq(Int))[2]""") { rewriterType: SMTEncoding =>
    val tup = intSeq(3.to(5): _*)

    val state = new SymbState(tup, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val seq = nextState.asCell
    val eq1 = tla.eql(intSeqAt(seqCell(seq), 1), tla.int(3))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = tla.eql(intSeqAt(seqCell(seq), 2), tla.int(4))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = tla.eql(intSeqAt(seqCell(seq), 3), tla.int(5))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
  }

  test("""(<<>> as Seq(Int))[1]""") { rewriterType: SMTEncoding =>
    // regression: <<>>[i] should produce no contradiction, nor throw an exception
    val tup = intSeq()
    val app = intSeqAt(tup, 1)

    val state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    val _ = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""(<<>> as Seq(Int))[x] when x = 1""") { rewriterType: SMTEncoding =>
    // regression: <<>>[i] should produce no contradiction, nor throw an exception
    val tup = intSeq()
    val app = tla.app(tup, tla.name("x", IntT1))

    var state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    // rewrite 1 into a cell, so function application does not statically detect out of bounds
    state = rewriter.rewriteUntilDone(state.setRex(tla.int(1)))
    state = state.setBinding(Binding("x" -> state.asCell))
    val _ = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""(<<1, 2>> as Seq(Int))[7]""") { rewriterType: SMTEncoding =>
    // regression: <<1, 2>>[i] for i = 7 should produce no contradiction, nor throw an exception
    val tup = intSeq(1, 2)
    val app = intSeqAt(tup, 7)

    val state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    val _ = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""(<<1, 2>> as Seq(Int))[x] for x = 7""") { rewriterType: SMTEncoding =>
    // regression: <<1, 2>>[i] for i = 7 should produce no contradiction, nor throw an exception
    val tup = intSeq(1, 2)
    val app = tla.app(tup, tla.name("x", IntT1))

    var state = new SymbState(app, arena, Binding())
    val rewriter = create(rewriterType)
    // rewrite 7 into a cell, so function application does not statically detect out of bounds
    state = rewriter.rewriteUntilDone(state.setRex(tla.int(7)))
    state = state.setBinding(Binding("x" -> state.asCell))
    val _ = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""Head(<<3, 4, 5>> as Seq(Int))""") { rewriterType: SMTEncoding =>
    val tup = intSeq(3.to(5): _*)
    val seqHead = tla.head(tup)
    val eq = tla.eql(seqHead, tla.int(3))

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Len(<<3, 4, 5>> <: Seq(Int))""") { rewriterType: SMTEncoding =>
    val tup = intSeq(3.to(5): _*)
    val seqLen = tla.len(tup)
    val eq = tla.eql(seqLen, tla.int(3))

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Tail(<<3, 4, 5>> as Seq(Int))""") { rewriterType: SMTEncoding =>
    val tup = intSeq(3.to(5): _*)
    val seqTail = tla.tail(tup)
    val expected = intSeq(4, 5)
    val eq = tla.eql(seqTail, expected)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Tail(<<>> as Seq(Int)) throws an error""") { rewriterType: SMTEncoding =>
    // Tail(<<>>) returns <<>>. Since Tail(<<>>) is undefined, it is a correct behavior.
    val emptyTuple = intSeq()
    val seqTail = tla.tail(emptyTuple)
    val eq = tla.eql(tla.len(seqTail), tla.int(0))
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""regression: Tail(SubSeq(<<1>>, 1, 0)) does not unsat and its length is -1""") { rewriterType: SMTEncoding =>
    val tuple1 = intSeq(1)
    val seqTail = tla.tail(tla.subseq(tuple1, tla.int(1), tla.int(0)))
    // One can argue that the Len(Tail(seqTail)) should be 0,
    // but Tail is undefined on empty sequences, so we are free to report -1.
    val eq = tla.eql(tla.len(seqTail), tla.int(-1))

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<3, 4, 5, 6>>, 2, 3)""") { rewriterType: SMTEncoding =>
    val tup = intSeq(3.to(6): _*)
    val subseqEx = tla.subseq(tup, tla.int(2), tla.int(3))

    val state = new SymbState(subseqEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(CellTFrom(SeqT1(IntT1)) == result.cellType)
    val eq1 = tla.eql(intSeqAt(seqCell(result), 1), tla.int(4))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = tla.eql(intSeqAt(seqCell(result), 2), tla.int(5))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = tla.eql(tla.len(seqCell(result)), tla.int(2))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
  }

  test("""regression: SubSeq(<<3, 4, 5, 6>>, 3, 1) does not unsat and has length 0""") { rewriterType: SMTEncoding =>
    val tup = intSeq(3.to(6): _*)
    val subseqEx = tla.subseq(tup, tla.int(3), tla.int(1))
    val eq = tla.eql(tla.len(subseqEx), tla.int(0))

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<3, 4, 5, 6>>, 5, 6) does not unsat and has length 0""") { rewriterType: SMTEncoding =>
    val tup = intSeq(3.to(6): _*)
    val subseqEx = tla.subseq(tup, tla.int(5), tla.int(6))
    val eq = tla.eql(tla.len(subseqEx), tla.int(0))

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<3, 4, 5, 6>>, 1, 10) = <<3, 4, 5, 6>>""") { rewriterType: SMTEncoding =>
    val tup = intSeq(3.to(6): _*)
    val subseqEx = tla.subseq(tup, tla.int(1), tla.int(10))
    val eq = tla.eql(subseqEx, tup)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<3, 4, 5, 6>>, 0, 4) = <<3, 4, 5, 6>>""") { rewriterType: SMTEncoding =>
    // TLC throws an error in this case. We cannot produce side effects, so we are doing the best we can do here.
    val tup = intSeq(3.to(6): _*)
    val subseqEx = tla.subseq(tup, tla.int(0), tla.int(10))
    val eq = tla.eql(subseqEx, tup)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<3, 4, 5, 6>>, 1, 0) = <<>>""") { rewriterType: SMTEncoding =>
    // TLC throws an error in this case. We cannot produce side effects, so we are doing the best we can do here.
    val tup = intSeq(3.to(6): _*)
    val subseqEx = tla.subseq(tup, tla.int(1), tla.int(0))
    val eq = tla.eql(subseqEx, intSeq())

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<1, 2, 3>>, 1, 2) = SubSeq(<<1, 2, 4>>, 1, 2)""") { rewriterType: SMTEncoding =>
    val seq123 = intSeq(1, 2, 3)
    val subseqEx1 = tla.subseq(seq123, tla.int(1), tla.int(2))
    val seq124 = intSeq(1, 2, 4)
    val subseqEx2 = tla.subseq(seq124, tla.int(1), tla.int(2))
    val eq = tla.eql(subseqEx1, subseqEx2)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(<<1, 2, 3>>, 1, 3) /= SubSeq(<<1, 2, 4>>, 1, 3)""") { rewriterType: SMTEncoding =>
    val seq123 = intSeq(1, 2, 3)
    val seq124 = intSeq(1, 2, 4)
    val subseqEx1 = tla.subseq(seq123, tla.int(1), tla.int(3))
    val subseqEx2 = tla.subseq(seq124, tla.int(1), tla.int(3))
    val eq = tla.eql(subseqEx1, subseqEx2)
    val neq = tla.not(eq)

    val state = new SymbState(neq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Append(<<4, 5>>, 10)""") { rewriterType: SMTEncoding =>
    val tup = intSeq(4.to(5): _*)
    val seqAppend = tla.append(tup, tla.int(10))

    val state = new SymbState(seqAppend, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(CellTFrom(SeqT1(IntT1)) == result.cellType)
    val eq1 = tla.eql(intSeqAt(seqCell(result), 1), tla.int(4))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = tla.eql(intSeqAt(seqCell(result), 2), tla.int(5))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = tla.eql(intSeqAt(seqCell(result), 3), tla.int(10))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
    val eq4 = tla.eql(tla.len(seqCell(result)), tla.int(3))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq4))
  }

  test("""Append(SubSeq(S, 2, 3), 10)""") { rewriterType: SMTEncoding =>
    val tup = intSeq(3.to(6): _*)
    val subseqEx = tla.subseq(tup, tla.int(2), tla.int(3))
    val seqAppend = tla.append(subseqEx, tla.int(10))

    val state = new SymbState(seqAppend, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(CellTFrom(SeqT1(IntT1)) == result.cellType)
    val eq1 = tla.eql(intSeqAt(seqCell(result), 1), tla.int(4))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = tla.eql(intSeqAt(seqCell(result), 2), tla.int(5))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = tla.eql(intSeqAt(seqCell(result), 3), tla.int(10))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
    val eq4 = tla.eql(tla.len(seqCell(result)), tla.int(3))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq4))
  }

  test("""<<4, 5>> = SubSeq(<<3, 4, 5, 6>>, 2, 3)""") { rewriterType: SMTEncoding =>
    val tup3456 = intSeq(3.to(6): _*)
    val subseqEx = tla.subseq(tup3456, tla.int(2), tla.int(3))
    val tup45 = intSeq(4.to(5): _*)
    val eq = tla.eql(tup45, subseqEx)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""DOMAIN SubSeq(<<3, 4, 5, 6>>, 2, 3) equals {1, 2}""") { rewriterType: SMTEncoding =>
    val tup3456 = intSeq(3.to(6): _*)
    val subseqEx = tla.subseq(tup3456, tla.int(2), tla.int(3))
    val domEx = tla.dom(subseqEx)
    val eq = tla.eql(domEx, tla.enumSet(tla.int(1), tla.int(2)))

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""<<9, 10>> \o SubSeq(<<3, 4, 5, 6>>, 2, 3)""") { rewriterType: SMTEncoding =>
    val tup3_6 = intSeq(3.to(6): _*)
    val subseqRes = tla.subseq(tup3_6, tla.int(2), tla.int(3)) // <<4, 5>>
    val tup9_10 = intSeq(9, 10)
    val concatRes = tla.concat(tup9_10, subseqRes)
    val expected = intSeq(9, 10, 4, 5)
    val eq = tla.eql(concatRes, expected)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""regression: <<9, 10>> \o Tail(<<>>) does not unsat""") { rewriterType: SMTEncoding =>
    val t9_10 = intSeq(9, 10)
    val t1 = intSeq(1)
    // Tail(SubSeq(<<1>>, 1, 0)) produces some undefined value. In this case, \o should also produce an undefined value.
    val concatRes = tla.concat(t9_10, tla.tail(tla.subseq(t1, tla.int(1), tla.int(0))))

    val state = new SymbState(concatRes, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteUntilDone(state)
    // the result is undefined, but it should be sat
    assert(solverContext.sat())
  }

  test("""(<<3, 4, 5, 6>> EXCEPT ![2] = 7) = <<3, 7, 5, 6>>""") { rewriterType: SMTEncoding =>
    val tup3to6 = intSeq(3.to(6): _*)
    val tup3756 = intSeq(3, 7, 5, 6)
    val exceptEx = tla.except(tup3to6, tla.int(2), tla.int(7))
    val eq = tla.eql(exceptEx, tup3756)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""(<<3, 4, 5, 6>> EXCEPT ![10] = 7) = <<3, 4, 5, 6>>""") { rewriterType: SMTEncoding =>
    val tup3to6 = intSeq(3.to(6): _*)
    val exceptEx = tla.except(tup3to6, tla.int(10), tla.int(7))
    // since 10 does not belong to the domain, the sequence does not change
    val eq = tla.eql(exceptEx, tup3to6)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""(<< >> EXCEPT ![10] = 7) = << >>""") { rewriterType: SMTEncoding =>
    val emptyTuple = intSeq()
    val exceptEx = tla.except(emptyTuple, tla.int(10), tla.int(7))
    // since 10 does not belong to the domain, the sequence does not change
    val eq = tla.eql(exceptEx, emptyTuple)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""(ApalacheSeqCapacity(<<3, 4, 5, 6>>) = 4""") { rewriterType: SMTEncoding =>
    val seq3to6 = intSeq(3.to(6): _*)
    val ex = OperEx(ApalacheInternalOper.apalacheSeqCapacity, seq3to6.build)(Typed(IntT1))
    val eq = tla.eql(tla.unchecked(ex), tla.int(4))

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  // for PICK see TestCherryPick
}
