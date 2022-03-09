package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, ExprGradeStoreImpl}
import at.forsyte.apalache.tla.bmcmt.rewriter.MetricProfilerListener
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.rules._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * This class extends SymbStateRewriterImpl with encoding rules for the encoding with SMT arrays.
 *
 * @param _solverContext
 *   a fresh solver context that will be populated with constraints
 * @param exprGradeStore
 *   a labeling scheme that associated a grade with each expression; it is required to distinguish between state-level
 *   and action-level expressions.
 * @param profilerListener
 *   optional listener that is used to profile the rewriting rules
 * @author
 *   Rodrigo Otoni
 */
class SymbStateRewriterImplWithArrays(
    _solverContext: SolverContext,
    exprGradeStore: ExprGradeStore = new ExprGradeStoreImpl(),
    profilerListener: Option[MetricProfilerListener] = None)
    extends SymbStateRewriterImpl(_solverContext, exprGradeStore, profilerListener) {

  @transient
  override lazy val ruleLookupTable: Map[String, List[RewritingRule]] = defaultRuleLookupTable ++ newRules

  val newRules: Map[String, List[RewritingRule]] = {
    Map(
        // sets
        key(tla.in(tla.name("x"), tla.name("S")))
          -> List(new SetInRuleWithArrays(this)), // TODO: add support for funSet later
        key(tla.apalacheSelectInSet(tla.name("x"), tla.name("S")))
          -> List(new SetInRuleWithArrays(this)),
        key(tla.apalacheSelectInFun(tla.name("x"), tla.name("F")))
          -> List(new SetInRuleWithArrays(this)),
        key(tla.subseteq(tla.name("x"), tla.name("S")))
          -> List(new SetInclusionRuleWithArrays(this)),
        // TODO: consider copying one array and storing the edges of the other in SetCupRule
        // functions
        key(tla.funDef(tla.name("e"), tla.name("x"), tla.name("S")))
          -> List(new FunCtorRuleWithArrays(this)),
        key(tla.appFun(tla.name("f"), tla.name("x")))
          -> List(new FunAppRuleWithArrays(this)),
        key(tla.except(tla.name("f"), tla.int(1), tla.int(42)))
          -> List(new FunExceptRuleWithArrays(this)),
        key(tla.dom(tla.funDef(tla.name("e"), tla.name("x"), tla.name("S"))))
          -> List(new DomainRuleWithArrays(this, intRangeCache)),
    )
  }
}
