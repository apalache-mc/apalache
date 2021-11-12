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
        key(NameEx("x"))
          -> List(substRule),
        key(tla.prime(NameEx("x")))
          -> List(new PrimeRule(this)),
        // assignment
        key(OperEx(ApalacheOper.assign, tla.name("x"), tla.name("y")))
          -> List(new AssignmentRule(this)),
        // constants
        key(ValEx(TlaBool(true)))
          -> List(new BuiltinConstRule(this)),
        key(ValEx(TlaBoolSet))
          -> List(new BuiltinConstRule(this)),
        key(ValEx(TlaIntSet))
          -> List(new BuiltinConstRule(this)),
        key(ValEx(TlaNatSet))
          -> List(new BuiltinConstRule(this)),
        key(ValEx(TlaInt(1)))
          -> List(new IntConstRule(this)),
        key(ValEx(TlaStr("red")))
          -> List(new StrConstRule(this)),
        // logic
        key(tla.eql(tla.name("x"), tla.name("y")))
          -> List(new EqRuleWithArrays(this)), // TODO: update with additional elements later
        key(tla.or(tla.name("x"), tla.name("y")))
          -> List(new OrRule(this)),
        key(tla.and(tla.name("x"), tla.name("y")))
          -> List(new AndRule(this)),
        key(tla.not(tla.name("x")))
          -> List(new NegRule(this)),
        // sets
        key(tla.in(tla.name("x"), tla.name("S")))
          -> List(new SetInRuleWithArrays(this)), // TODO: add support for funSet later
        key(tla.enumSet(tla.name("x")))
          -> List(new SetCtorRule(this)),
        key(tla.subseteq(tla.name("x"), tla.name("S")))
          -> List(new SetInclusionRuleWithArrays(this)),
        key(tla.cup(tla.name("X"), tla.name("Y")))
          -> List(new SetCupRule(this)), // TODO: consider copying one array and storing the edges of the other
        key(tla.filter(tla.name("x"), tla.name("S"), tla.name("p")))
          -> List(new SetFilterRule(this)),
        key(tla.map(tla.name("e"), tla.name("x"), tla.name("S")))
          -> List(new SetMapRule(this)),
        key(OperEx(ApalacheOper.expand, tla.name("X")))
          -> List(new SetExpandRule(this)),
        key(tla.powSet(tla.name("X")))
          -> List(new PowSetCtorRule(this)),
        key(tla.union(tla.enumSet()))
          -> List(new SetUnionRule(this)),
        key(tla.dotdot(tla.int(1), tla.int(10)))
          -> List(new IntDotDotRule(this, intRangeCache)),
        // integers
        key(tla.lt(tla.int(1), tla.int(2)))
          -> List(new IntCmpRule(this)),
        key(tla.le(tla.int(1), tla.int(2)))
          -> List(new IntCmpRule(this)),
        key(tla.gt(tla.int(1), tla.int(2)))
          -> List(new IntCmpRule(this)),
        key(tla.ge(tla.int(1), tla.int(2)))
          -> List(new IntCmpRule(this)),
        key(tla.plus(tla.int(1), tla.int(2)))
          -> List(new IntArithRule(this)),
        key(tla.minus(tla.int(1), tla.int(2)))
          -> List(new IntArithRule(this)),
        key(tla.mult(tla.int(1), tla.int(2)))
          -> List(new IntArithRule(this)),
        key(tla.div(tla.int(1), tla.int(2)))
          -> List(new IntArithRule(this)),
        key(tla.mod(tla.int(1), tla.int(2)))
          -> List(new IntArithRule(this)),
        key(tla.exp(tla.int(2), tla.int(3)))
          -> List(new IntArithRule(this)),
        key(tla.uminus(tla.int(1)))
          -> List(new IntArithRule(this)),
        // -----------------------------------------------------------------
        // RULES BELOW WERE ADDED TO RUN UNIT TESTS, WILL BE LOOKED AT LATER
        // -----------------------------------------------------------------
        // logic
        key(OperEx(ApalacheOper.skolem, tla.exists(tla.name("x"), tla.name("S"), tla.name("p"))))
          -> List(new QuantRule(this)),
        key(tla.exists(tla.name("x"), tla.name("S"), tla.name("p")))
          -> List(new QuantRule(this)),
        key(tla.forall(tla.name("x"), tla.name("S"), tla.name("p")))
          -> List(new QuantRule(this)),
        // control flow
        key(tla.ite(tla.name("cond"), tla.name("then"), tla.name("else")))
          -> List(new IfThenElseRule(this)),
        // functions
        key(tla.funDef(tla.name("e"), tla.name("x"), tla.name("S")))
          -> List(new FunCtorRule(this)),
        key(tla.appFun(tla.name("f"), tla.name("x")))
          -> List(new FunAppRule(this)),
        // tuples, records, and sequences
        key(tla.tuple(tla.name("x"), tla.int(2)))
          -> List(new TupleOrSeqCtorRule(this)),
        key(tla.enumFun(tla.str("a"), tla.int(2)))
          -> List(new RecCtorRule(this))
    )
  }
}
