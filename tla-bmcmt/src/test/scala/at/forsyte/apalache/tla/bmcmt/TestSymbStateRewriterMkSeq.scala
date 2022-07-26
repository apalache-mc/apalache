package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._

trait TestSymbStateRewriterMkSeq extends RewriterBase {
  test("""MkSeq(3, LAMBDA x: x + 1) = << 2, 3, 4 >>""") { rewriterType: SMTEncoding =>
    // A(x) == x + 1
    val intT = IntT1
    val seqT = SeqT1(intT)
    val opT = OperT1(Seq(intT), intT)

    val plusOneEx = plus(name("x").as(intT), int(1)).as(intT)
    val plusOneOper = TlaOperDecl("A", List(OperParam("x")), plusOneEx)(Typed(opT))
    val letEx = LetInEx(name(plusOneOper.name).typed(opT), plusOneOper)(Typed(opT))
    val seqEx = apalacheMkSeq(int(3), letEx).as(seqT)
    val rewriter = create(rewriterType)
    var state = new SymbState(seqEx, arena, Binding())
    state = rewriter.rewriteUntilDone(state.setRex(seqEx))
    val seqCell = state.asCell

    // compare the length
    val eqn = eql(len(seqCell.toNameEx).as(intT), int(3)).as(BoolT1)
    assertTlaExAndRestore(rewriter, state.setRex(eqn))

    // compare the elements
    for (i <- 1.to(3)) {
      val eqn = eql(appFun(seqCell.toNameEx, int(i)).as(intT), int(i + 1)).as(BoolT1)
      assertTlaExAndRestore(rewriter, state.setRex(eqn))
    }
  }

  test("""MkSeq(0, LAMBDA x: x + 1) = << >>""") { rewriterType: SMTEncoding =>
    // A(x) == x + 1
    val intT = IntT1
    val seqT = SeqT1(intT)
    val opT = OperT1(Seq(intT), intT)

    val plusOneEx = plus(name("x").as(intT), int(1)).as(intT)
    val plusOneOper = TlaOperDecl("A", List(OperParam("x")), plusOneEx)(Typed(opT))
    val letEx = LetInEx(name(plusOneOper.name).typed(opT), plusOneOper)(Typed(opT))
    val seqEx = apalacheMkSeq(int(0), letEx).as(seqT)

    val eqn = eql(len(seqEx).as(intT), int(0)).as(BoolT1)
    val state = new SymbState(eqn, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }
}
