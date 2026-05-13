package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterControl extends RewriterBase {
  test("""IF 3 > 2 THEN 2 < 4 ELSE 5 < 1""") { rewriterType: SMTEncoding =>
    val pred = tla.gt(tla.int(3), tla.int(2))
    val e1 = tla.lt(tla.int(2), tla.int(4))
    val e2 = tla.lt(tla.int(5), tla.int(1))
    val ifThenElse = tla.ite(pred, e1, e2)

    val state = new SymbState(ifThenElse, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state.setRex(ifThenElse))
  }

  test("""IF 3 < 2 THEN 2 < 4 ELSE 5 < 1""") { rewriterType: SMTEncoding =>
    val pred = tla.lt(tla.int(3), tla.int(2))
    val e1 = tla.lt(tla.int(2), tla.int(4))
    val e2 = tla.lt(tla.int(5), tla.int(1))
    val ifThenElse = tla.not(tla.ite(pred, e1, e2))

    val state = new SymbState(ifThenElse, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state.setRex(ifThenElse))
  }

  test("""IF 3 > 2 THEN 4 ELSE 1""") { rewriterType: SMTEncoding =>
    val pred = tla.gt(tla.int(3), tla.int(2))
    val e1 = tla.int(4)
    val e2 = tla.int(1)
    val ifThenElse = tla.ite(pred, e1, e2)
    val eq4 = tla.eql(ifThenElse, tla.int(4))

    val state = new SymbState(eq4, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""IF 3 < 2 THEN 4 ELSE 1""") { rewriterType: SMTEncoding =>
    val pred = tla.lt(tla.int(3), tla.int(2))
    val e1 = tla.int(4)
    val e2 = tla.int(1)
    val ifThenElse = tla.ite(pred, e1, e2)
    val eq4 = tla.eql(ifThenElse, tla.int(1))

    val state = new SymbState(eq4, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""IF 3 < 2 THEN {1, 2} ELSE {2, 3} equals {2, 3}""") { rewriterType: SMTEncoding =>
    val pred = tla.lt(tla.int(3), tla.int(2))
    val e1 = tla.enumSet(tla.int(1), tla.int(2))
    val e2 = tla.enumSet(tla.int(2), tla.int(3))
    val ifThenElse = tla.ite(pred, e1, e2)
    val eq23 = tla.eql(ifThenElse, e2)

    val state = new SymbState(eq23, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""IF 1 = 1 THEN {2} ELSE {1} ]""") { rewriterType: SMTEncoding =>
    val ifThenElse = tla.ite(tla.eql(tla.int(1), tla.int(1)), tla.enumSet(tla.int(2)), tla.enumSet(tla.int(1)))
    val eq = tla.eql(tla.enumSet(tla.int(2)), ifThenElse)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""SE-ITE[5]: IF 2 < 3 THEN {1, 2} ELSE {2, 3} ~~> {1, 2}""") { rewriterType: SMTEncoding =>
    val pred = tla.lt(tla.int(2), tla.int(3))
    val e1 = tla.enumSet(tla.int(1), tla.int(2))
    val e2 = tla.enumSet(tla.int(2), tla.int(3))
    val ifThenElse = tla.ite(pred, e1, e2)
    val eq = tla.eql(ifThenElse, e1)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""1 + (IF 3 < 2 THEN 4 ELSE 1)""") { rewriterType: SMTEncoding =>
    val pred = tla.lt(tla.int(3), tla.int(2))
    val e1 = tla.int(4)
    val e2 = tla.int(1)
    val addition = tla.plus(tla.int(1), tla.ite(pred, e1, e2))
    val eq = tla.eql(addition, tla.int(2))

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  // LET-IN is often used to cache computation results
  test("""LET A == 1 + 2 IN 1 + A equals 4""") { rewriterType: SMTEncoding =>
    val decl = tla.decl("A", tla.plus(tla.int(1), tla.int(2)))
    val let = tla.letIn(tla.plus(tla.int(1), tla.appOp(tla.name("A", OperT1(Seq(), IntT1)))), decl)
    val state = new SymbState(let, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val eq = tla.eql(tla.unchecked(nextState.ex), tla.int(4))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }
}
