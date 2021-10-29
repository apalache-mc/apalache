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
        key(tla.eql(tla.name("x"), tla.name("y"))) // TODO
          -> List(new EqRule(this)),
        key(tla.or(tla.name("x"), tla.name("y"))) // OK
          -> List(new OrRule(this)),
        key(tla.and(tla.name("x"), tla.name("y"))) // OK
          -> List(new AndRule(this)),
        key(tla.not(tla.name("x"))) // OK
          -> List(new NegRule(this)),
        // sets
        key(tla.in(tla.name("x"), tla.name("S"))) // TODO
          -> List(new SetInRule(this)),
        key(tla.enumSet(tla.name("x"))) // OK
          -> List(new SetCtorRule(this)),
        key(tla.subseteq(tla.name("x"), tla.name("S"))) // TODO
          -> List(new SetInclusionRule(this)),
        // TODO: Potential optimization of SetCupRule: copy the largest array and only store edges for the smaller one.
        key(tla.cup(tla.name("X"), tla.name("Y"))) // OK
          -> List(new SetCupRule(this)),
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
