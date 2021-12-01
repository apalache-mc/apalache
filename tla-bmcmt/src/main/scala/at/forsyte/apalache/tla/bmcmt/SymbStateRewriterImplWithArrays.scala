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
 * TODO: enforce that _solverContext.config.smtEncoding is correct?
 *
 * @param _solverContext   a fresh solver context that will be populated with constraints
 * @param exprGradeStore   a labeling scheme that associated a grade with each expression;
 *                         it is required to distinguish between state-level and action-level expressions.
 * @param profilerListener optional listener that is used to profile the rewriting rules
 * @author Rodrigo Otoni
 */
class SymbStateRewriterImplWithArrays(_solverContext: SolverContext,
    exprGradeStore: ExprGradeStore = new ExprGradeStoreImpl(), profilerListener: Option[MetricProfilerListener] = None)
    extends SymbStateRewriterImpl(_solverContext, exprGradeStore, profilerListener) {

  // TODO: remove unsupportedRules after passing over all rules
  @transient
  override lazy val ruleLookupTable: Map[String, List[RewritingRule]] =
    (defaultRuleLookupTable ++ newRules) -- unsupportedRules.keys

  val newRules: Map[String, List[RewritingRule]] = {
    Map(
        // logic
        key(tla.eql(tla.name("x"), tla.name("y")))
          -> List(new EqRuleWithArrays(this)), // TODO: update with additional elements later
        // sets
        key(tla.in(tla.name("x"), tla.name("S")))
          -> List(new SetInRuleWithArrays(this)), // TODO: add support for funSet later
        key(tla.subseteq(tla.name("x"), tla.name("S")))
          -> List(new SetInclusionRuleWithArrays(this))
        // TODO: consider copying one array and storing the edges of the other in SetCupRule
    )
  }

  val unsupportedRules: Map[String, List[RewritingRule]] = {
    Map(
        // logic
        key(tla.choose(tla.name("x"), tla.name("S"), tla.name("p")))
          -> List(new ChooseRule(this)),
        // control flow
        key(tla.letIn(tla.int(1), TlaOperDecl("A", List(), tla.int(2))))
          -> List(new LetInRule(this)),
        key(tla.appDecl(TlaOperDecl("userOp", List(), tla.int(3)))) ->
          List(new UserOperRule(this)),
        // functions
        key(tla.except(tla.name("f"), tla.int(1), tla.int(42)))
          -> List(new FunExceptRule(this)),
        key(tla.funSet(tla.name("X"), tla.name("Y")))
          -> List(new FunSetCtorRule(this)),
        key(tla.dom(tla.funDef(tla.name("e"), tla.name("x"), tla.name("S"))))
          -> List(new DomainRule(this, intRangeCache)), // also works for records
        key(tla.recFunDef(tla.name("e"), tla.name("x"), tla.name("S")))
          -> List(new RecFunDefAndRefRule(this)),
        key(tla.recFunRef())
          -> List(new RecFunDefAndRefRule(this)),
        // tuples, records, and sequences
        key(tla.head(tla.tuple(tla.name("x"))))
          -> List(new SeqOpsRule(this)),
        key(tla.tail(tla.tuple(tla.name("x"))))
          -> List(new SeqOpsRule(this)),
        key(tla.subseq(tla.tuple(tla.name("x")), tla.int(2), tla.int(4)))
          -> List(new SeqOpsRule(this)),
        key(tla.len(tla.tuple(tla.name("x"))))
          -> List(new SeqOpsRule(this)),
        key(tla.append(tla.tuple(tla.name("x")), tla.int(10)))
          -> List(new SeqOpsRule(this)),
        key(tla.concat(tla.name("Seq1"), tla.name("Seq2")))
          -> List(new SeqOpsRule(this)),
        // FiniteSets
        key(OperEx(ApalacheOper.constCard, tla.ge(tla.card(tla.name("S")), tla.int(3))))
          -> List(new CardinalityConstRule(this)),
        key(OperEx(TlaFiniteSetOper.cardinality, tla.name("S")))
          -> List(new CardinalityRule(this)),
        key(OperEx(TlaFiniteSetOper.isFiniteSet, tla.name("S")))
          -> List(new IsFiniteSetRule(this)),
        // misc
        key(OperEx(TlaOper.label, tla.str("lab"), tla.str("x")))
          -> List(new LabelRule(this)),
        key(OperEx(ApalacheOper.gen, tla.int(2)))
          -> List(new GenRule(this)),
        // folds
        key(OperEx(ApalacheOper.foldSet, tla.name("A"), tla.name("v"), tla.name("S")))
          -> List(new FoldSetRule(this)),
        key(OperEx(ApalacheOper.foldSeq, tla.name("A"), tla.name("v"), tla.name("s")))
          -> List(new FoldSeqRule(this)),
        // TLC
        key(OperEx(TlcOper.print, tla.bool(true), tla.str("msg")))
          -> List(new TlcRule(this)),
        key(OperEx(TlcOper.printT, tla.str("msg")))
          -> List(new TlcRule(this)),
        key(OperEx(TlcOper.assert, tla.bool(true), tla.str("msg")))
          -> List(new TlcRule(this)),
        key(OperEx(TlcOper.colonGreater, tla.int(1), tla.int(2))) // :>
          -> List(new TlcRule(this)),
        key(OperEx(TlcOper.atat, NameEx("fun"), NameEx("pair"))) // @@
          -> List(new TlcRule(this))
        // -----------------------------------------------------------------------
        // RULES BELOW WERE NOT REMOVED TO RUN UNIT TESTS, WILL BE LOOKED AT LATER
        // -----------------------------------------------------------------------
        /*
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
         */
    )
  }
}
