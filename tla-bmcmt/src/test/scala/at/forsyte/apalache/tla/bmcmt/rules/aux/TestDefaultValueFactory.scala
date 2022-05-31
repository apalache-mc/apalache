package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import at.forsyte.apalache.tla.bmcmt.{Binding, RewriterBase, SMTEncoding, SymbState}
import at.forsyte.apalache.tla.lir.TypedPredefs.BuilderExAsTyped
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.{BoolT1, TestingPredefs}

trait TestDefaultValueFactory extends RewriterBase with TestingPredefs {
  private val parser = DefaultType1Parser

  test("""create a record""") { rewriterType: SMTEncoding =>
    val recordT = parser("{ a: Int, b: Bool }")
    val rewriter = create(rewriterType)
    val factory = new DefaultValueFactory(rewriter)
    val (newArena, value) = factory.makeUpValue(arena, recordT)
    assert(solverContext.sat())

    val expected = enumFun(str("a"), int(0), str("b"), bool(false)).as(recordT)
    val eq = eql(expected, value.toNameEx).as(BoolT1)
    val state = new SymbState(eq, newArena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }
}
