package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux

import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.lir.TlaEx

/**
 * A mock context, which just intercepts any expression added via assertGroundExpr and stores it in a Seq.
 *
 * We can use it in tests, to observe constraint generation without needing to instrument SMT.
 */
class MockZ3SolverContext extends Z3SolverContext(SolverConfig.default) {
  var constraints: Seq[TlaEx] = Seq.empty
  override def assertGroundExpr(ex: TlaEx): Unit = constraints = constraints :+ ex
}
