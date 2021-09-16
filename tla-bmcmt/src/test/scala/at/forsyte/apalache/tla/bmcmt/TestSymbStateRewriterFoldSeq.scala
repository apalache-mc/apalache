package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.rules.FoldSeqRule
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterFoldSeq extends RewriterBase {

  test("""FoldSeq( LAMBDA x,y: C, v, S ) = C""") {
    // A : (a,b) => a
    // A(p,q) == 0
    val a = IntT1()
    val b = IntT1()
    val opT = OperT1(Seq(a, b), a)

    val nonemptySeq = tuple(int(2), int(3)).typed(SeqT1(b))

    def constVal = int(0)

    val nullOperDecl = declOp("A", constVal, OperParam("p"), OperParam("q")) as opT
    val letEx = LetInEx(name(nullOperDecl.name).typed(opT), nullOperDecl)(Typed(opT))

    val foldEx = OperEx(
        ApalacheOper.foldSeq,
        letEx,
        int(1).typed(IntT1()),
        nonemptySeq
    )(Typed(a))

    val eqn = eql(foldEx, constVal).typed(BoolT1())

    val state = new SymbState(eqn, arena, Binding())

    assert(new FoldSeqRule(this.create()).isApplicable(state.setRex(foldEx)))

    assertTlaExAndRestore(create(), state)
  }

  test("""FoldSeq( LAMBDA x,y: ..., v, <<>> ) = v""") {
    // A : (a,b) => a
    // A(p,q) == 0
    val a = IntT1()
    val b = IntT1()
    val opT = OperT1(Seq(a, b), a)

    val emptySeq = tuple().typed(SeqT1(b))

    val nullOperDecl = declOp("A", int(0), OperParam("p"), OperParam("q")) as opT
    val letEx = LetInEx(name(nullOperDecl.name).typed(opT), nullOperDecl)(Typed(opT))

    def v = int(1).typed(IntT1())

    val foldEx = OperEx(
        ApalacheOper.foldSeq,
        letEx,
        v,
        emptySeq
    )(Typed(a))

    val eqn = eql(foldEx, v).typed(BoolT1())

    val state = new SymbState(eqn, arena, Binding())

    assertTlaExAndRestore(create(), state)
  }

  test("""FoldSeq( LAMBDA x,y: x + 1, 0, s ) = Card(Len(s))""") {
    // A : (a,b) => a
    // A(p,q) == p + 1
    val a = IntT1()
    val b = StrT1()
    val opT = OperT1(Seq(a, b), a)

    val nonemptySeq = tuple(str("x"), str("y")).typed(SeqT1(b))
    val plusOneOper = TlaOperDecl(
        "A",
        List(OperParam("p"), OperParam("q")),
        plus(name("p").typed(a), int(1)).typed(IntT1())
    )(Typed(opT))

    val letEx = LetInEx(name(plusOneOper.name).typed(opT), plusOneOper)(Typed(opT))

    val foldEx = OperEx(
        ApalacheOper.foldSeq,
        letEx,
        int(0).typed(IntT1()),
        nonemptySeq
    )(Typed(a))

    val eqn = eql(foldEx, len(nonemptySeq).typed(IntT1())).typed(BoolT1())

    val state = new SymbState(eqn, arena, Binding())

    assertTlaExAndRestore(create(), state)
  }

  test("""FoldSeq( LAMBDA x,y: x + y, 0, s ) = Sum(s)""") {
    // A : (a,b) => a
    // A(p,q) == p + q
    val a = IntT1()
    val b = IntT1()
    val opT = OperT1(Seq(a, b), a)

    val ints = Seq(2, 93, 4)
    val nonemptySeq = tuple(ints map int: _*).typed(SeqT1(b))

    val plusOneOper = TlaOperDecl(
        "A",
        List(OperParam("p"), OperParam("q")),
        plus(name("p").typed(a), name("q").typed(b)).typed(IntT1())
    )(Typed(opT))

    val letEx = LetInEx(name(plusOneOper.name).typed(opT), plusOneOper)(Typed(opT))

    val foldEx = OperEx(
        ApalacheOper.foldSeq,
        letEx,
        int(0).typed(IntT1()),
        nonemptySeq
    )(Typed(a))

    val eqn = eql(foldEx, int(ints.sum)).typed(BoolT1())

    val state = new SymbState(eqn, arena, Binding())

    assertTlaExAndRestore(create(), state)
  }
}
