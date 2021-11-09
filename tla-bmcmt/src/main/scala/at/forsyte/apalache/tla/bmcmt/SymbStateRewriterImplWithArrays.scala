package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, ExprGradeStoreImpl}
import at.forsyte.apalache.tla.bmcmt.rewriter.MetricProfilerListener
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.rules._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaBoolSet, TlaInt, TlaIntSet, TlaNatSet, TlaStr}
import at.forsyte.apalache.tla.lir.UntypedPredefs._

class SymbStateRewriterImplWithArrays(_solverContext: SolverContext,
    exprGradeStore: ExprGradeStore = new ExprGradeStoreImpl(), profilerListener: Option[MetricProfilerListener] = None)
    extends SymbStateRewriterImpl(_solverContext, exprGradeStore, profilerListener) {

  // TODO: after passing over all rules, use super.ruleLookupTable and overwrite modified rules
  @transient
  override lazy val ruleLookupTable: Map[String, List[RewritingRule]] = {
    Map(
        // the order is only important to improve readability

        // substitution
        key(NameEx("x")) // OK
          -> List(substRule),
        key(tla.prime(NameEx("x"))) // OK
          -> List(new PrimeRule(this)),
        // assignment
        key(OperEx(ApalacheOper.assign, tla.name("x"), tla.name("y"))) // OK
          -> List(new AssignmentRule(this)),
        // constants
        key(ValEx(TlaBool(true))) // OK
          -> List(new BuiltinConstRule(this)),
        key(ValEx(TlaBoolSet)) // OK
          -> List(new BuiltinConstRule(this)),
        key(ValEx(TlaIntSet)) // OK
          -> List(new BuiltinConstRule(this)),
        key(ValEx(TlaNatSet)) // OK
          -> List(new BuiltinConstRule(this)),
        key(ValEx(TlaInt(1))) // OK
          -> List(new IntConstRule(this)),
        key(ValEx(TlaStr("red"))) // OK
          -> List(new StrConstRule(this)),
        // logic
        key(tla.eql(tla.name("x"), tla.name("y"))) // OK
          -> List(new EqRuleWithArrays(this)), // TODO: update with additional elements later
        key(tla.or(tla.name("x"), tla.name("y"))) // OK
          -> List(new OrRule(this)),
        key(tla.and(tla.name("x"), tla.name("y"))) // OK
          -> List(new AndRule(this)),
        key(tla.not(tla.name("x"))) // OK
          -> List(new NegRule(this)),
        // sets
        key(tla.in(tla.name("x"), tla.name("S"))) // OK
          -> List(new SetInRuleWithArrays(this)), // TODO: add support for funSet later
        // TODO: (potential SetCtorRule optimization) remove redundant "select" assertions
        key(tla.enumSet(tla.name("x"))) // OK
          -> List(new SetCtorRule(this)),
        key(tla.subseteq(tla.name("x"), tla.name("S"))) // OK
          -> List(new SetInclusionRuleWithArrays(this)),
        // TODO: (potential SetCupRule optimization) copy the largest array and only store edges for the smaller one
        key(tla.cup(tla.name("X"), tla.name("Y"))) // OK
          -> List(new SetCupRule(this)),
        key(tla.filter(tla.name("x"), tla.name("S"), tla.name("p"))) // TODO
          -> List(new SetFilterRule(this)),
        key(tla.map(tla.name("e"), tla.name("x"), tla.name("S"))) // TODO
          -> List(new SetMapRule(this)),
        // TODO: (potential SetExpandRule optimization) remove redundant "select" assertions in PowSetCtor.confringo
        key(OperEx(ApalacheOper.expand, tla.name("X"))) // OK
          -> List(new SetExpandRule(this)),
        key(tla.powSet(tla.name("X"))) // OK
          -> List(new PowSetCtorRule(this)),
        // TODO: (potential IntDotDotRule optimization) remove redundant "select" assertions in intRangeCache.create
        key(tla.dotdot(tla.int(1), tla.int(10))) // OK
          -> List(new IntDotDotRule(this, intRangeCache)),
        // integers
        key(tla.lt(tla.int(1), tla.int(2))) // OK
          -> List(new IntCmpRule(this)),
        key(tla.le(tla.int(1), tla.int(2))) // OK
          -> List(new IntCmpRule(this)),
        key(tla.gt(tla.int(1), tla.int(2))) // OK
          -> List(new IntCmpRule(this)),
        key(tla.ge(tla.int(1), tla.int(2))) // OK
          -> List(new IntCmpRule(this)),
        key(tla.plus(tla.int(1), tla.int(2))) // OK
          -> List(new IntArithRule(this)),
        key(tla.minus(tla.int(1), tla.int(2))) // OK
          -> List(new IntArithRule(this)),
        key(tla.mult(tla.int(1), tla.int(2))) // OK
          -> List(new IntArithRule(this)),
        key(tla.div(tla.int(1), tla.int(2))) // OK
          -> List(new IntArithRule(this)),
        key(tla.mod(tla.int(1), tla.int(2))) // OK
          -> List(new IntArithRule(this)),
        key(tla.exp(tla.int(2), tla.int(3))) // OK
          -> List(new IntArithRule(this)),
        key(tla.uminus(tla.int(1))) // OK
          -> List(new IntArithRule(this))
    )
  }
}
