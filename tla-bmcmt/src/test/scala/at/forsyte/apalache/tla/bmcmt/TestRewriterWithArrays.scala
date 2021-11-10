package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.smt.{PreproSolverContext, SolverConfig, Z3SolverContext}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatest.junit.JUnitRunner

// TODO: Extend rewriter tests gradually as development in the "arrays" encoding progresses

@RunWith(classOf[JUnitRunner])
class TestRewriterWithArrays
    extends TestSymbStateRewriter with TestSymbStateRewriterInt with TestSymbStateRewriterSet
    with TestSymbStateRewriterStr {
  override protected def withFixture(test: OneArgTest): Outcome = {
    solverContext = new PreproSolverContext(new Z3SolverContext(SolverConfig.default.copy(debug = true,
                smtEncoding = arraysEncodingType)))
    arena = Arena.create(solverContext)
    val result = test(arraysEncodingType)
    solverContext.dispose()
    result
  }
}
