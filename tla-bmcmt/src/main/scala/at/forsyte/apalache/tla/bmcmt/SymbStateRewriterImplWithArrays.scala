package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, ExprGradeStoreImpl}
import at.forsyte.apalache.tla.bmcmt.rewriter.MetricProfilerListener
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext

class SymbStateRewriterImplWithArrays(_solverContext: SolverContext,
    exprGradeStore: ExprGradeStore = new ExprGradeStoreImpl(), profilerListener: Option[MetricProfilerListener] = None)
    extends SymbStateRewriterImpl(_solverContext, exprGradeStore, profilerListener) {}
