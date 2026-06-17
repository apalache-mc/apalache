package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.rules.FoldSetRule
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterFoldSet extends RewriterBase {
  test("""FoldSet( LAMBDA x,y: C, v, S ) = C""") { rewriterType: SMTEncoding =>
    // A : (a,b) => a
    // A(p,q) == 0
    val a = IntT1
    val b = IntT1
    val nonemptySet = tla.enumSet(tla.int(2), tla.int(3))

    def constVal = tla.int(0)

    val letEx = tla.lambda("A", constVal, tla.param("p", a), tla.param("q", b))
    val foldEx = tla.foldSet(letEx, tla.int(1), nonemptySet)
    val eqn = tla.eql(foldEx, constVal)

    val state = new SymbState(eqn, arena, Binding())

    assert(new FoldSetRule(this.create(rewriterType), renaming).isApplicable(state.setRex(foldEx.build)))

    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""FoldSet( LAMBDA x,y: ..., v, {} ) = v""") { rewriterType: SMTEncoding =>
    // A : (a,b) => a
    // A(p,q) == 0
    val a = IntT1
    val b = IntT1
    val emptySet = tla.emptySet(b)
    val letEx = tla.lambda("A", tla.int(0), tla.param("p", a), tla.param("q", b))

    def v = tla.int(1)
    val foldEx = tla.foldSet(letEx, v, emptySet)

    val eqn = tla.eql(foldEx, v)

    val state = new SymbState(eqn, arena, Binding())

    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""FoldSet( LAMBDA x,y: x + 1, 0, S ) = Card(S)""") { rewriterType: SMTEncoding =>
    // A : (a,b) => a
    // A(p,q) == p + 1
    val a = IntT1
    val b = StrT1
    // insert duplicate x
    val nonemptySet = tla.enumSet(tla.str("x"), tla.str("x"), tla.str("y"))
    val plusOneBody = tla.plus(tla.name("p", a), tla.int(1))
    val letEx = tla.lambda("A", plusOneBody, tla.param("p", a), tla.param("q", b))
    val foldEx = tla.foldSet(letEx, tla.int(0), nonemptySet)
    val eqn = tla.eql(foldEx, tla.cardinality(nonemptySet))

    val state = new SymbState(eqn, arena, Binding())

    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""FoldSet( LAMBDA x,y: x + y, 0, S ) = Sum(S)""") { rewriterType: SMTEncoding =>
    // A : (a,b) => a
    // A(p,q) == p + q
    val a = IntT1
    val b = IntT1
    val ints = Seq(2, 93, 4)
    val nonemptySet = tla.enumSet(ints.map(i => tla.int(i)): _*)
    val plusBody = tla.plus(tla.name("p", a), tla.name("q", b))
    val letEx = tla.lambda("A", plusBody, tla.param("p", a), tla.param("q", b))
    val foldEx = tla.foldSet(letEx, tla.int(0), nonemptySet)
    val eqn = tla.eql(foldEx, tla.int(ints.sum))

    val state = new SymbState(eqn, arena, Binding())

    assertTlaExAndRestore(create(rewriterType), state)
  }
}
