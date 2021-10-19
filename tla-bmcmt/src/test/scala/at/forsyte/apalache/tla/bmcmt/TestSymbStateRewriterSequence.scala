package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterSequence extends RewriterBase {
  private val types = Map(
      "i" -> IntT1(),
      "I" -> SetT1(IntT1()),
      "b" -> BoolT1(),
      "Qi" -> SeqT1(IntT1())
  )

  // As sequences are not distinguishable from tuples, we need a type annotation.
  // In the not so far away future, a type inference engine would tell us, whether to construct a sequence or a tuple
  test("""<<>> as Seq(Int)""") { rewriterType: String =>
    val tup = tuple()
      .typed(types, "Qi")

    val state = new SymbState(tup, arena, Binding())
    val nextState = create(rewriterType).rewriteUntilDone(state)
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

  test("""<<1, 2, 3>> as Seq(Int)""") { rewriterType: String =>
    val tup = tuple(1.to(3).map(int): _*)
      .typed(types, "Qi")

    val state = new SymbState(tup, arena, Binding())
    val nextState = create(rewriterType).rewriteUntilDone(state)
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

  test("""(<<3, 4, 5>> as Seq(Int))[2]""") { rewriterType: String =>
    val tup = tuple(3.to(5).map(int): _*)
      .typed(types, "Qi")

    val state = new SymbState(tup, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val seq = nextState.asCell
    val eq1 = eql(appFun(seq.toNameEx ? "Qi", int(1)) ? "i", int(3))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = eql(appFun(seq.toNameEx ? "Qi", int(2)) ? "i", int(4))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = eql(appFun(seq.toNameEx ? "Qi", int(3)) ? "i", int(5))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
  }

  test("""(<<>> as Seq(Int))[1]""") { rewriterType: String =>
    // regression: <<>>[1] should produce no contradiction, nor throw an exception
    val tup = tuple()
      .typed(types, "Qi")

    val state = new SymbState(tup, arena, Binding())
    val rewriter = create(rewriterType)
    val _ = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""Head(<<3, 4, 5>> as Seq(Int))""") { rewriterType: String =>
    val tup = tuple(3.to(5).map(int): _*) ? "Qi"
    val seqHead = head(tup) ? "i"
    val eq = eql(seqHead, int(3))
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Len(<<3, 4, 5>> <: Seq(Int))""") { rewriterType: String =>
    val tup = tuple(3.to(5).map(i => int(i)): _*)
      .typed(types, "Qi")
    val seqLen = len(tup) ? "i"
    val eq = eql(seqLen, int(3))
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Tail(<<3, 4, 5>> as Seq(Int))""") { rewriterType: String =>
    val tup = tuple(3.to(5).map(int): _*) ? "Qi"
    val seqTail = tail(tup) ? "Qi"
    val expected = tuple(int(4), int(5)) ? "Qi"
    val eq = eql(seqTail, expected)
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""regression: Tail(<<>> as Seq(Int)) does not unsat and its length is zero""") { rewriterType: String =>
    val emptyTuple = tuple()
      .typed(types, "Qi")
    val seqTail = tail(emptyTuple)
      .typed(types, "Qi")
    val eq = eql(len(seqTail) ? "i", int(0))
      .typed(types, "i")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SubSeq(S, 2, 4)""") { rewriterType: String =>
    val tup = tuple(3.to(6).map(int): _*)
      .typed(types, "Qi")
    val subseqEx = subseq(tup, int(2), int(3))
      .typed(types, "Qi")

    val state = new SymbState(subseqEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(SeqT(IntT()) == result.cellType)
    val eq1 = eql(appFun(result.toNameEx ? "Qi", int(1)) ? "i", int(4))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = eql(appFun(result.toNameEx ? "Qi", int(2)) ? "i", int(5))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = eql(len(result.toNameEx ? "Qi") ? "i", int(2))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
  }

  test("""regression: SubSeq(S, 3, 1) does not unsat and has length 0""") { rewriterType: String =>
    val tup = tuple(3.to(6).map(int): _*)
      .typed(types, "Qi")
    val subseqEx = subseq(tup, int(3), int(1))
      .typed(types, "Qi")
    val eq = eql(len(subseqEx) ? "i", int(0))
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Append(S, 10)""") { rewriterType: String =>
    val tup = tuple(4.to(5).map(int): _*)
      .typed(types, "Qi")
    val seqAppend = append(tup, int(10))
      .typed(types, "Qi")

    val state = new SymbState(seqAppend, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(SeqT(IntT()) == result.cellType)
    val eq1 = eql(appFun(result.toNameEx ? "Qi", int(1)) ? "i", int(4))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = eql(appFun(result.toNameEx ? "Qi", int(2)) ? "i", int(5))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = eql(appFun(result.toNameEx ? "Qi", int(3)) ? "i", int(10))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
    val eq4 = eql(len(result.toNameEx ? "Qi") ? "i", int(3)).typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq4))
  }

  test("""Append(SubSeq(S, 2, 3), 10)""") { rewriterType: String =>
    val tup = tuple(3.to(6).map(int): _*) ? "Qi"
    val subseqEx = subseq(tup, int(2), int(3)) ? "Qi"
    val seqAppend = append(subseqEx, int(10))
      .typed(types, "Qi")

    val state = new SymbState(seqAppend, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val result = nextState.asCell
    assert(SeqT(IntT()) == result.cellType)
    val eq1 = eql(appFun(result.toNameEx ? "Qi", int(1)) ? "i", int(4))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq1))
    val eq2 = eql(appFun(result.toNameEx ? "Qi", int(2)) ? "i", int(5))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq2))
    val eq3 = eql(appFun(result.toNameEx ? "Qi", int(3)) ? "i", int(10))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq3))
    val eq4 = eql(len(result.toNameEx ? "Qi") ? "i", int(3)).typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq4))
  }

  test("""<<4, 5>> = SubSeq(<<3, 4, 5, 6>>, 2, 3)""") { rewriterType: String =>
    val tup3456 = tuple(3.to(6).map(int): _*) ? "Qi"
    val subseqEx = subseq(tup3456, int(2), int(3)) ? "Qi"
    val tup45 = tuple(4.to(5).map(int): _*) ? "Qi"
    val eq = eql(tup45, subseqEx)
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""DOMAIN SubSeq(<<3, 4, 5, 6>>, 2, 3) equals {2, 3}""") { rewriterType: String =>
    val tup3456 = tuple(3.to(6).map(int): _*) ? "Qi"
    val subseqEx = subseq(tup3456, int(2), int(3)) ? "Qi"
    val domEx = dom(subseqEx) ? "I"
    val eq = eql(domEx, enumSet(int(2), int(3)) ? "I")
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""<<9, 10>> \o SubSeq(S, 2, 3)""") { rewriterType: String =>
    val tup3_6 = tuple(3.to(6).map(int): _*) ? "Qi"
    val subseqRes = subseq(tup3_6, int(2), int(3)) ? "Qi" // <<4, 5>>
    val tup9_10 = tuple(int(9), int(10)) ? "Qi"
    val concatRes = concat(tup9_10, subseqRes) ? "Qi"
    val expected = tuple(int(9), int(10), int(4), int(5)) ? "Qi"
    val eq = eql(concatRes, expected)
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""regression: <<9, 10>> \o Tail(<<>>) does not unsat""") { rewriterType: String =>
    val t9_10 = tuple(int(9), int(10)) ? "Qi"
    // Tail(<<>>) produces some undefined value. In this case, \o should also produce an undefined value.
    val concatRes = concat(t9_10, tail(tuple() ? "Qi") ? "Qi")
      .typed(types, "Qi")

    val state = new SymbState(concatRes, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // the result is undefined, but it should be sat
    assert(solverContext.sat())
  }

  // for PICK see TestCherryPick
}
