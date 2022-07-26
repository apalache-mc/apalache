package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.rules.FoldSetRule
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.ApalacheOper

trait TestSymbStateRewriterFoldSet extends RewriterBase {
  test("""FoldSet( LAMBDA x,y: C, v, S ) = C""") { rewriterType: SMTEncoding =>
    // A : (a,b) => a
    // A(p,q) == 0
    val a = IntT1
    val b = IntT1
    val opT = OperT1(Seq(a, b), a)

    val nonemptySet = enumSet(int(2), int(3)).typed(SetT1(b))

    def constVal = int(0)

    val nullOperDecl = declOp("A", constVal, OperParam("p"), OperParam("q")).as(opT)
    val letEx = LetInEx(name(nullOperDecl.name).typed(opT), nullOperDecl)(Typed(opT))

    val foldEx = OperEx(
        ApalacheOper.foldSet,
        letEx,
        int(1).typed(IntT1),
        nonemptySet,
    )(Typed(a))

    val eqn = eql(foldEx, constVal).typed(BoolT1)

    val state = new SymbState(eqn, arena, Binding())

    assert(new FoldSetRule(this.create(rewriterType), renaming).isApplicable(state.setRex(foldEx)))

    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""FoldSet( LAMBDA x,y: ..., v, {} ) = v""") { rewriterType: SMTEncoding =>
    // A : (a,b) => a
    // A(p,q) == 0
    val a = IntT1
    val b = IntT1
    val opT = OperT1(Seq(a, b), a)

    val emptySet = enumSet().typed(SetT1(b))

    val nullOperDecl = declOp("A", int(0), OperParam("p"), OperParam("q")).as(opT)
    val letEx = LetInEx(name(nullOperDecl.name).typed(opT), nullOperDecl)(Typed(opT))

    def v = int(1).typed(IntT1)
    val foldEx = OperEx(
        ApalacheOper.foldSet,
        letEx,
        v,
        emptySet,
    )(Typed(a))

    val eqn = eql(foldEx, v).typed(BoolT1)

    val state = new SymbState(eqn, arena, Binding())

    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""FoldSet( LAMBDA x,y: x + 1, 0, S ) = Card(S)""") { rewriterType: SMTEncoding =>
    // A : (a,b) => a
    // A(p,q) == p + 1
    val a = IntT1
    val b = StrT1
    val opT = OperT1(Seq(a, b), a)

    // insert duplicate x
    val nonemptySet = enumSet(str("x"), str("x"), str("y")).typed(SetT1(b))
    val plusOneOper = TlaOperDecl(
        "A",
        List(OperParam("p"), OperParam("q")),
        plus(name("p").typed(a), int(1)).typed(IntT1),
    )(Typed(opT))

    val letEx = LetInEx(name(plusOneOper.name).typed(opT), plusOneOper)(Typed(opT))

    val foldEx = OperEx(
        ApalacheOper.foldSet,
        letEx,
        int(0).typed(IntT1),
        nonemptySet,
    )(Typed(a))

    val eqn = eql(foldEx, card(nonemptySet).typed(IntT1)).typed(BoolT1)

    val state = new SymbState(eqn, arena, Binding())

    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""FoldSet( LAMBDA x,y: x + y, 0, S ) = Sum(S)""") { rewriterType: SMTEncoding =>
    // A : (a,b) => a
    // A(p,q) == p + q
    val a = IntT1
    val b = IntT1
    val opT = OperT1(Seq(a, b), a)

    val ints = Seq(2, 93, 4)
    val nonemptySet = enumSet(ints.map(int): _*).typed(SetT1(b))

    val plusOneOper = TlaOperDecl(
        "A",
        List(OperParam("p"), OperParam("q")),
        plus(name("p").typed(a), name("q").typed(b)).typed(IntT1),
    )(Typed(opT))

    val letEx = LetInEx(name(plusOneOper.name).typed(opT), plusOneOper)(Typed(opT))

    val foldEx = OperEx(
        ApalacheOper.foldSet,
        letEx,
        int(0).typed(IntT1),
        nonemptySet,
    )(Typed(a))

    val eqn = eql(foldEx, int(ints.sum)).typed(BoolT1)

    val state = new SymbState(eqn, arena, Binding())

    assertTlaExAndRestore(create(rewriterType), state)
  }
}
