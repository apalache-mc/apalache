package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux

import at.forsyte.apalache.tla.bmcmt.stratifiedRules._
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.apalache.AssignmentStratifiedRule
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.base.{BuiltinConstStratifiedRule, SubstStratifiedRule}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.set.{SetCtorStratifiedRule, SetCupStratifiedRule}
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.bool.{AndStratifiedRule, OrStratifiedRule}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.types.tla
import scalaz.unused

/**
 * Rewrite a TLA+ expression into a graph of cells (Arena).
 *
 * This is the central access point to the rewriting rules.
 *
 * As a by-product, implementations may use a [[at.forsyte.apalache.tla.bmcmt.smt.SolverContext]] and produce SMT
 * constraints over the computed Arena cells.
 *
 * TODO: SolverContext is unused in the interim, but will be present in the final version.
 *
 * @author
 *   Jure Kukovec
 */
abstract class RewriterImpl(@unused private val ctx: SolverContext) extends Rewriter {

  override def assert(ex: TlaEx): Unit = {
    // TODO: For now, we don't actually use `ctx` yet
    // ctx.assertGroundExpr(ex)
  }

  /**
   * Compute a key of a TLA+ expression to quickly decide on a short sequence of rules to try.
   *
   * @param ex
   *   a TLA+ expression
   * @return
   *   a string that gives us an equivalence class for similar operations (see the code)
   */
  protected def key(ex: TlaEx): String = ex match {
    case OperEx(TlaOper.apply, NameEx(_), _*) => "U@"
    case OperEx(oper, _*)                     => "O@" + oper.name
    case LetInEx(_, _*)                       => "L@"
    case ValEx(TlaInt(_))                     => "I@"
    case ValEx(TlaIntSet)                     => "SI@"
    case ValEx(TlaNatSet)                     => "SN@"
    case ValEx(TlaBool(_))                    => "B@"
    case ValEx(TlaBoolSet)                    => "SB@"
    case NameEx(_)                            => "N@"
    case _                                    => "O@"
  }

  // A nice way to guess the candidate rules by looking at the expression key.
  // We use simple expressions to generate the keys.
  // For each key, there is a short list of rules that may be applicable.
  val ruleLookupTable: Map[String, StratifiedRuleInterface] = {
    Map(
        // - the order is only important to improve readability
        // - types don't matter for lookup, but are required by the builder

        // substitution
        key(tla.name("x", IntT1)) -> new SubstStratifiedRule,
//      key(tla.prime(NameEx("x")))
//        -> List(new PrimeRule),
//      // assignment
        key(tla.assign(tla.prime(tla.name("x", IntT1)), tla.name("y", IntT1)))
          -> new AssignmentStratifiedRule(this),
//      // constants
        key(tla.bool(true))
          -> new BuiltinConstStratifiedRule,
        key(tla.booleanSet())
          -> new BuiltinConstStratifiedRule,
        key(tla.intSet())
          -> new BuiltinConstStratifiedRule,
        key(tla.natSet())
          -> new BuiltinConstStratifiedRule,
//        key(ValEx(TlaInt(1)))
//        -> List(new IntConstRule(this)),
//      key(ValEx(TlaStr("red")))
//        -> List(new StrConstRule(this)),
//      // logic
//      key(tla.eql(tla.name("x"), tla.name("y")))
//        -> List(new EqRule(this)),
        key(tla.or(tla.name("x", BoolT1), tla.name("y", BoolT1)))
          -> new OrStratifiedRule(this),
        key(tla.and(tla.name("x", BoolT1), tla.name("y", BoolT1)))
          -> new AndStratifiedRule(this),
//      key(tla.not(tla.name("x")))
//        -> List(new NegRule(this)),
//      key(OperEx(ApalacheOper.skolem, tla.exists(tla.name("x"), tla.name("S"), tla.name("p"))))
//        -> List(new QuantRule(this)),
//      key(tla.exists(tla.name("x"), tla.name("S"), tla.name("p")))
//        -> List(new QuantRule(this)),
//      key(tla.forall(tla.name("x"), tla.name("S"), tla.name("p")))
//        -> List(new QuantRule(this)),
//      key(tla.choose(tla.name("x"), tla.name("S"), tla.name("p")))
//        -> List(new ChooseOrGuessRule(this)),
//      key(tla.guess(tla.name("S")))
//        -> List(new ChooseOrGuessRule(this)),
//      // control flow
//      key(tla.ite(tla.name("cond"), tla.name("then"), tla.name("else")))
//        -> List(new IfThenElseRule(this)),
//      key(tla.letIn(tla.int(1), TlaOperDecl("A", List(), tla.int(2))))
//        -> List(new LetInRule(this)),
//      // TODO, rethink TlaOper.apply rule
//      key(tla.appDecl(TlaOperDecl("userOp", List(), tla.int(3)))) ->
//        List(new UserOperRule(this)),
//      // sets
//      key(tla.in(tla.name("x"), tla.name("S")))
//        -> List(new SetInRule(this)),
//      key(tla.apalacheSelectInSet(tla.name("x"), tla.name("S")))
//        -> List(new SetInRule(this)),
        key(tla.enumSet(tla.name("x", IntT1)))
          -> new SetCtorStratifiedRule(this),
        key(tla.cup(tla.name("X", SetT1(IntT1)), tla.name("Y", SetT1(IntT1))))
          -> new SetCupStratifiedRule(this),
//        key(tla.filter(tla.name("x", IntT1), tla.name("S", SetT1(IntT1)), tla.name("p", BoolT1)))
//          -> new SetFilterStratifiedRule(this),
//      key(tla.map(tla.name("e"), tla.name("x"), tla.name("S")))
//        -> List(new SetMapRule(this)),
//      key(OperEx(ApalacheOper.expand, tla.name("X")))
//        -> List(new SetExpandRule(this)),
//      key(tla.powSet(tla.name("X")))
//        -> List(new PowSetCtorRule(this)),
//      key(tla.union(tla.enumSet()))
//        -> List(new SetUnionRule(this)),
//      key(tla.dotdot(tla.int(1), tla.int(10)))
//        -> List(new IntDotDotRule(this, intRangeCache)),
//      // integers
//      key(tla.lt(tla.int(1), tla.int(2)))
//        -> List(new IntCmpRule(this)),
//      key(tla.le(tla.int(1), tla.int(2)))
//        -> List(new IntCmpRule(this)),
//      key(tla.gt(tla.int(1), tla.int(2)))
//        -> List(new IntCmpRule(this)),
//      key(tla.ge(tla.int(1), tla.int(2)))
//        -> List(new IntCmpRule(this)),
//      key(tla.plus(tla.int(1), tla.int(2)))
//        -> List(new IntArithRule(this)),
//      key(tla.minus(tla.int(1), tla.int(2)))
//        -> List(new IntArithRule(this)),
//      key(tla.mult(tla.int(1), tla.int(2)))
//        -> List(new IntArithRule(this)),
//      key(tla.div(tla.int(1), tla.int(2)))
//        -> List(new IntArithRule(this)),
//      key(tla.mod(tla.int(1), tla.int(2)))
//        -> List(new IntArithRule(this)),
//      key(tla.exp(tla.int(2), tla.int(3)))
//        -> List(new IntArithRule(this)),
//      key(tla.uminus(tla.int(1)))
//        -> List(new IntArithRule(this)),
//      // functions
//        key(tla.funDef(tla.name("e", IntT1), tla.name("x", IntT1) -> tla.name("S", SetT1(IntT1))))
//          -> new FunCtorStratifiedRule(this),
//      key(tla.appFun(tla.name("f"), tla.name("x")))
//        -> List(new FunAppRule(this)),
//      key(tla.except(tla.name("f"), tla.int(1), tla.int(42)))
//        -> List(new FunExceptRule(this)),
//      key(tla.funSet(tla.name("X"), tla.name("Y")))
//        -> List(new FunSetCtorRule(this)),
//      key(tla.dom(tla.funDef(tla.name("e"), tla.name("x"), tla.name("S"))))
//        -> List(new DomainRule(this, intRangeCache)), // also works for records
//      // tuples, records, and sequences
//      key(tla.tuple(tla.name("x"), tla.int(2)))
//        -> List(new TupleOrSeqCtorRule(this)),
//      key(tla.enumFun(tla.str("a"), tla.int(2)))
//        -> List(new RecCtorRule(this)),
//      key(tla.head(tla.tuple(tla.name("x"))))
//        -> List(new SeqOpsRule(this)),
//      key(tla.tail(tla.tuple(tla.name("x"))))
//        -> List(new SeqOpsRule(this)),
//      key(tla.subseq(tla.tuple(tla.name("x")), tla.int(2), tla.int(4)))
//        -> List(new SeqOpsRule(this)),
//      key(tla.len(tla.tuple(tla.name("x"))))
//        -> List(new SeqOpsRule(this)),
//      key(OperEx(ApalacheInternalOper.apalacheSeqCapacity, tla.name("seq")))
//        -> List(new SeqOpsRule(this)),
//      key(tla.append(tla.tuple(tla.name("x")), tla.int(10)))
//        -> List(new SeqOpsRule(this)),
//      key(tla.concat(tla.name("Seq1"), tla.name("Seq2")))
//        -> List(new SeqOpsRule(this)),
//      key(tla.apalacheSetAsFun(tla.enumSet()))
//        -> List(new SetAsFunRule(this)),
//      // variants
//      key(tla.variant("Tag", tla.int(33)))
//        -> List(new VariantOpsRule(this)),
//      key(tla.variantGetUnsafe("Tag", tla.name("V")))
//        -> List(new VariantOpsRule(this)),
//      key(tla.variantGetOrElse("Tag", tla.name("V"), tla.name("def")))
//        -> List(new VariantOpsRule(this)),
//      key(tla.variantTag(tla.name("V")))
//        -> List(new VariantOpsRule(this)),
//      key(tla.variantFilter("Tag", tla.name("S")))
//        -> List(new VariantOpsRule(this)),
//      // FiniteSets
//      key(OperEx(ApalacheOper.constCard, tla.ge(tla.card(tla.name("S")), tla.int(3))))
//        -> List(new CardinalityConstRule(this)),
//      key(OperEx(TlaFiniteSetOper.cardinality, tla.name("S")))
//        -> List(new CardinalityRule(this)),
//      key(OperEx(TlaFiniteSetOper.isFiniteSet, tla.name("S")))
//        -> List(new IsFiniteSetRule(this)),
//      // misc
//      key(OperEx(TlaOper.label, tla.str("lab"), tla.str("x")))
//        -> List(new LabelRule(this)),
//      key(OperEx(ApalacheOper.gen, tla.int(2)))
//        -> List(new GenRule(this)),
//      // folds and MkSeq
//      key(OperEx(ApalacheOper.foldSet, tla.name("A"), tla.name("v"), tla.name("S")))
//        -> List(new FoldSetRule(this, renaming)),
//      key(OperEx(ApalacheOper.foldSeq, tla.name("A"), tla.name("v"), tla.name("s")))
//        -> List(new FoldSeqRule(this, renaming)),
//      key(OperEx(ApalacheOper.mkSeq, tla.int(10), tla.name("A")))
//        -> List(new MkSeqRule(this, renaming)),
    )
  } ///// ADD YOUR RULES ABOVE

}
