package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.{Binding, RewriterBase, SymbState}
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.types.tla

trait TestDefaultValueFactory extends RewriterBase {
  private val parser = DefaultType1Parser

  test("""create a record""") { rewriterType: SMTEncoding =>
    val recordT = parser("{ a: Int, b: Bool }")
    val rewriter = create(rewriterType)
    val factory = new DefaultValueFactory(rewriter)
    val (newArena, value) = factory.makeUpValue(arena, recordT)
    assert(solverContext.sat())

    val expected = tla.rowRec(None, "a" -> tla.int(0), "b" -> tla.bool(false))
    val eq = tla.eql(expected, tla.unchecked(value.toNameEx))
    val state = new SymbState(eq, newArena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }
}
