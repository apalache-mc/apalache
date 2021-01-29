package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter.{Continue, Done, NoRule, RewritingResult}
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.caches._
import at.forsyte.apalache.tla.bmcmt.profiler.RuleStatListener
import at.forsyte.apalache.tla.bmcmt.rewriter.{MetricProfilerListener, Recoverable, RewriterConfig, SymbStateRewriterSnapshot}
import at.forsyte.apalache.tla.bmcmt.rules._
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.bmcmt.types.{CellT, TypeFinder}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBoolSet, TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}

import scala.collection.mutable

/**
  * <p>This class rewrites a symbolic state.
  * This is the place where all the action regarding the operational semantics is happening.</p>
  *
  * <p>This class implements StackableContext by delegating the respective operations to all the internal caches
  * and the SMT context. Thus, it is a central access point for context operations.</p>
  *
  * <p>TODO: rename this class to RewriterImpl?</p>
  *
  * @param _solverContext  a fresh solver context that will be populated with constraints
  * @param typeFinder     a type finder (assuming that typeFinder.inferAndSave has been called already)
  * @param exprGradeStore a labeling scheme that associated a grade with each expression;
  *                       it is required to distinguish between state-level and action-level expressions.
  * @param profilerListener optional listener that is used to profile the rewriting rules
  *
  * @author Igor Konnov
  */
class SymbStateRewriterImpl(private var _solverContext: SolverContext,
                            var typeFinder: TypeFinder[CellT],
                            val exprGradeStore: ExprGradeStore = new ExprGradeStoreImpl(),
                            val profilerListener: Option[MetricProfilerListener] = None
                           )
    extends SymbStateRewriter with Serializable with Recoverable[SymbStateRewriterSnapshot] {


  /**
    * <p>A solver context that is populated by the rewriter.</p>
    *
    * <p>This method will be removed when solving #105.</p>
    */
  override def solverContext: SolverContext = _solverContext

  /**
    * <p>Set the new solver context. Warning: the new context should be at the same stack depth as the rewriter.
    * Otherwise, pop may produce unexpected results.</p>
    *
    * <p>This method will be removed when solving #105.</p>
    *
    * @param newContext new context
    */
  override def solverContext_=(newContext: SolverContext): Unit = {
    _solverContext = newContext
  }

  /**
    * We collect the sequence of expressions in the rewriting process,
    * in order to diagnose an error when an exception occurs. The latest expression in on top.
    */
  private var rewritingStack: Seq[TlaEx] = Seq()

  /**
    * The difference between the number of pushes and pops so far.
    */
  private var level: Int = 0

  /**
    * Configuration options
    *
    * @return the rewriter options
    */
  var config: RewriterConfig = new RewriterConfig

  /**
    * The cache for lazy equalities, to avoid generating the same equality constraints many times.
    */
  val lazyEq = new LazyEquality(this)

  /**
    * A cache for integer literals.
    */
  val intValueCache = new IntValueCache(solverContext)

  /**
    * A cache for integer ranges a..b.
    */
  val intRangeCache = new IntRangeCache(solverContext, intValueCache)

  /**
    * A cache for string literals.
    */
  val strValueCache = new StrValueCache(solverContext)

  /**
    * A cache of record domains.
    */
  val recordDomainCache = new RecordDomainCache(solverContext, strValueCache)

  /**
    * An expression cache that is initialized by grade storage, by default, empty.
    * Set it to a new object, if you want to use a grade storage.
    */
  val exprCache = new ExprCache(exprGradeStore)

  @transient
  private lazy val substRule = new SubstRule(this)

  /**
    * The store that contains formula hints. By default, empty.
    */
  var formulaHintsStore: FormulaHintsStore = new FormulaHintsStoreImpl()

  /**
    * A storage for the messages associated with assertion failures, see MessageStorage.
    */
  private var messages: mutable.Map[Int, String] = new mutable.HashMap()

  /**
    * Get the current context level, that is the difference between the number of pushes and pops made so far.
    *
    * @return the current level, always non-negative.
    */
  def contextLevel: Int = level

  /**
    * Statistics listener
    *
    * TODO: remove this listener, as it does not seem to be compatible with serialization.
    * TODO: does this listener consume too many resources?
    */
  @transient
  lazy val statListener: RuleStatListener = new RuleStatListener()
  solverContext.setSmtListener(statListener) // subscribe to the SMT solver

  // A nice way to guess the candidate rules by looking at the expression key.
  // We use simple expressions to generate the keys.
  // For each key, there is a short list of rules that may be applicable.
  @transient
  lazy val ruleLookupTable: Map[String, List[RewritingRule]] = { Map(
    // the order is only important to improve readability

    // substitution
    key(NameEx("x"))
      -> List(substRule),
    key(tla.prime(NameEx("x")))
      -> List(new PrimeRule(this)),

    // assignment
    key( OperEx( BmcOper.assign, tla.name("x"), tla.name("y") ) )
      -> List( new AssignmentRule(this) ),

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
      -> List(new EqRule(this)),
    key(tla.or(tla.name("x"), tla.name("y")))
      -> List(new OrRule(this)),
    key(tla.and(tla.name("x"), tla.name("y")))
      -> List(new AndRule(this)),
    key(tla.not(tla.name("x")))
      -> List(new NegRule(this)),
    key(OperEx(BmcOper.skolem, tla.exists(tla.name("x"),
               tla.name("S"), tla.name("p"))))
      -> List(new QuantRule(this)),
    key(tla.exists(tla.name("x"), tla.name("S"), tla.name("p")))
      -> List(new QuantRule(this)),
    key(tla.forall(tla.name("x"), tla.name("S"), tla.name("p")))
      -> List(new QuantRule(this)),
    key(tla.choose(tla.name("x"), tla.name("S"), tla.name("p")))
      -> List(new ChooseRule(this)),

    // control flow
    key(tla.ite(tla.name("cond"), tla.name("then"), tla.name("else")))
      -> List(new IfThenElseRule(this)),
    key(tla.letIn(tla.int(1), TlaOperDecl("A", List(), tla.int(2))))
      -> List(new LetInRule(this)),
      // TODO, rethink TlaOper.apply rule
    key(tla.appDecl( TlaOperDecl("userOp", List(), tla.int(3)) ) ) ->
      List(new UserOperRule(this)),

    // sets
    key(tla.in(tla.name("x"), tla.name("S")))
      -> List( new SetInRule(this) ),
    key(tla.enumSet(tla.name("x"))) ->
      List(new SetCtorRule(this)),
    key(tla.subseteq(tla.name("x"), tla.name("S")))
      -> List(new SetInclusionRule(this)),
    key(tla.cup(tla.name("X"), tla.name("Y")))
      -> List(new SetCupRule(this)),
    key(tla.filter(tla.name("x"), tla.name("S"), tla.name("p")))
      -> List(new SetFilterRule(this)),
    key(tla.map(tla.name("e"), tla.name("x"), tla.name("S")))
      -> List(new SetMapRule(this)),
    key(OperEx(BmcOper.expand, tla.name("X")))
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

    // functions
    key(tla.funDef(tla.name("e"), tla.name("x"), tla.name("S")))
      -> List(new FunCtorRule(this)),
    key(tla.appFun(tla.name("f"), tla.name("x")))
      -> List(new FunAppRule(this)),
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
    key(tla.tuple(tla.name("x"), tla.int(2)))
      -> List(new TupleOrSeqCtorRule(this)),
    key(tla.enumFun(tla.str("a"), tla.int(2)))
      -> List(new RecCtorRule(this)),
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
    key(OperEx(BmcOper.constCard, tla.ge(tla.card(tla.name("S")), tla.int(3))))
      -> List(new CardinalityConstRule(this)),
    key(OperEx(TlaFiniteSetOper.cardinality, tla.name("S")))
      -> List(new CardinalityRule(this)),
    key(OperEx(TlaFiniteSetOper.isFiniteSet, tla.name("S")))
      -> List(new IsFiniteSetRule(this)),

    // misc
    key(OperEx(TlaOper.label, tla.str("lab"), tla.str("x")))
      -> List(new LabelRule(this)),
    key(OperEx(BmcOper.withType, tla.int(1), ValEx(TlaIntSet)))
      -> List(new TypeAnnotationRule(this)),

    // TLC
    key(OperEx(TlcOper.print, tla.bool(true), tla.str("msg")))
      -> List(new TlcRule(this)),
    key(OperEx(TlcOper.printT, tla.str("msg")))
      -> List(new TlcRule(this)),
    key(OperEx(TlcOper.assert, tla.bool(true), tla.str("msg")))
      -> List(new TlcRule(this)),
    key(OperEx(TlcOper.colonGreater, tla.int(1), tla.int(2))) // :>
      -> List(new TlcRule(this)),
    key(OperEx(TlcOper.atat, NameEx("fun"), NameEx("pair")))  // @@
      -> List(new TlcRule(this))
  ) } ///// ADD YOUR RULES ABOVE


  /**
    * Rewrite a symbolic expression by applying at most one rewriting rule.
    *
    * @param state a symbolic state
    * @return the new symbolic state obtained by rewriting state
    */
  def rewriteOnce(state: SymbState): RewritingResult = {
    state.ex match {
      case NameEx(name) if ArenaCell.isValidName(name) =>
        Done(state)

      case NameEx(name) =>
        if (substRule.isApplicable(state)) {
          statListener.enterRule(substRule.getClass.getSimpleName)
          // a variable that can be substituted with a cell
          var nextState = substRule.apply(substRule.logOnEntry(solverContext, state))
          nextState = substRule.logOnReturn(solverContext, nextState)
          if (nextState.arena.cellCount < state.arena.cellCount) {
            throw new RewriterException("Implementation error: the number of cells decreased from %d to %d"
              .format(state.arena.cellCount, nextState.arena.cellCount), state.ex)
          }
          statListener.exitRule()
          Done(nextState)
        } else {
          // oh-oh
          NoRule()
        }

      case _ =>
        // lookup for a short list of potentially applicable rules
        val potentialRules = ruleLookupTable.getOrElse(key(state.ex), List())

        potentialRules.find(r => r.isApplicable(state)) match {
          case Some(r) =>
            statListener.enterRule(r.getClass.getSimpleName)
            val nextState = r.logOnReturn(solverContext, r.apply(r.logOnEntry(solverContext, state)))
            if (nextState.arena.cellCount < state.arena.cellCount) {
              throw new RewriterException("Implementation error in rule %s: the number of cells decreased from %d to %d"
                .format(r.getClass.getSimpleName, state.arena.cellCount, nextState.arena.cellCount), state.ex)
            }
            statListener.exitRule()
            Continue(nextState)

          case None =>
            NoRule()
        }
    }
  }

  /**
    * Rewrite one expression until converged to a single cell, or no rule applies.
    *
    * @param state a state to rewrite
    * @return the final state
    * @throws RewriterException if no rule applies
    */
  def rewriteUntilDone(state: SymbState): SymbState = {
    // the main reason for using a recursive function here instead of a loop is that it is easier to debug
    def doRecursive(ncalls: Int, st: SymbState): SymbState = {
      if (ncalls >= Limits.RECURSION_LIMIT) {
        throw new RewriterException("Recursion limit of %d steps is reached. A cycle in the rewriting system?"
          .format(Limits.RECURSION_LIMIT), state.ex)
      } else {
        rewritingStack +:= state.ex // push the expression on the stack
        rewriteOnce(st) match {
          case Done(nextState) =>
            // converged to a single cell
            rewritingStack = rewritingStack.tail // pop the expression of the stack
            solverContext.checkConsistency(nextState.arena) // debugging
            nextState

          case Continue(nextState) =>
            // more translation steps are needed
            val result = doRecursive(ncalls + 1, nextState)
            rewritingStack = rewritingStack.tail // pop the expression of the stack
            result

          case NoRule() =>
            // no rule applies, a problem in the tool?
            throw new RewriterException("No rewriting rule applies to expression: " + st.ex, st.ex)
        }
      }
    }

    // use cache or compute a new expression
    exprCache.get(state.ex) match {
      case Some(eg: (TlaEx, ExprGrade.Value)) =>
        solverContext.log(s"; Using cached value ${eg._1} for expression ${state.ex}")
        state.setRex(eg._1)

      case None =>
        // Get the SMT metrics before translating the expression.
        // Note that we are not doing that in the recursive function,
        // as the new expressions there will not have source information.
        val smtWatermark = solverContext.metrics()
        val nextState = doRecursive(0, state)
        profilerListener.foreach{ _.onRewrite(state.ex, solverContext.metrics().delta(smtWatermark)) }
        exprCache.put(state.ex, nextState.ex) // the grade is not important
        nextState
    }
  }

  /**
    * Rewrite all expressions in a sequence.
    *
    * @param state a state to start with
    * @param es    a sequence of expressions to rewrite
    * @return a pair (the new state with the original expression, the rewritten expressions)
    */
  def rewriteSeqUntilDone(state: SymbState, es: Seq[TlaEx]): (SymbState, Seq[TlaEx]) = {
    var newState = state // it is easier to write this code with a side effect on the state
    // we should be very careful about propagating arenas here
    def eachExpr(e: TlaEx): TlaEx = {
      val ns = rewriteUntilDone(new SymbState(e, newState.arena, newState.binding))
      assert(ns.arena.cellCount >= newState.arena.cellCount)
      newState = ns
      ns.ex
    }

    val rewrittenExprs = es map eachExpr
    (newState.setRex(state.ex), rewrittenExprs)
  }

  /**
    * An extended version of rewriteSeqUntilDone, where expressions are accompanied with bindings.
    *
    * @param state a state to start with
    * @param es    a sequence of expressions to rewrite accompanied with bindings
    * @return a pair (the old state in a new context, the rewritten expressions)
    */
  def rewriteBoundSeqUntilDone(state: SymbState, es: Seq[(Binding, TlaEx)]): (SymbState, Seq[TlaEx]) = {
    var newState = state // it is easier to write this code with a side effect on the state
    // we should be very careful about propagating arenas here
    def eachExpr(be: (Binding, TlaEx)): TlaEx = {
      val ns = rewriteUntilDone(new SymbState(be._2, newState.arena, be._1))
      assert(ns.arena.cellCount >= newState.arena.cellCount)
      newState = ns
      ns.ex
    }

    val rewrittenExprs = es map eachExpr
    (newState.setRex(state.ex), rewrittenExprs)
  }

  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////


  /**
    * Take a snapshot and return it
    *
    * @return the snapshot
    */
  override def snapshot(): SymbStateRewriterSnapshot = {
    new SymbStateRewriterSnapshot(typeFinder.asInstanceOf[TrivialTypeFinder].snapshot(),
      intValueCache.snapshot(),
      intRangeCache.snapshot(), strValueCache.snapshot(), recordDomainCache.snapshot(), exprCache.snapshot())
  }

  /**
    * Recover a previously saved snapshot (not necessarily saved by this object).
    * Note that caches have a reference to SolverContext, which is not recovered!
    *
    * @param shot a snapshot
    */
  override def recover(shot: SymbStateRewriterSnapshot): Unit = {
    typeFinder.asInstanceOf[TrivialTypeFinder].recover(shot.typeFinderSnapshot)
    intValueCache.recover(shot.intValueCacheSnapshot)
    intRangeCache.recover(shot.intRangeCacheSnapshot)
    strValueCache.recover(shot.strValueCacheSnapshot)
    recordDomainCache.recover(shot.recordDomainCache)
    exprCache.recover(shot.exprCacheSnapshot)
  }
/**
    * Save the current context and push it on the stack for a later recovery with pop.
    */
  override def push(): Unit = {
    level += 1
    intValueCache.push()
    intRangeCache.push()
    strValueCache.push()
    recordDomainCache.push()
    lazyEq.push()
    exprCache.push()
    solverContext.push()
  }

  /**
    * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
    * to save only the latest context.
    */
  override def pop(): Unit = {
    assert(level > 0)
    intValueCache.pop()
    intRangeCache.pop()
    strValueCache.pop()
    recordDomainCache.pop()
    lazyEq.pop()
    exprCache.pop()
    solverContext.pop()
    level -= 1
  }

  /**
    * Call pop several times.
    *
    * @param n the number of times to call pop
    */
  override def pop(n: Int): Unit = {
    assert(level >= n)
    intValueCache.pop(n)
    intRangeCache.pop(n)
    strValueCache.pop(n)
    recordDomainCache.pop(n)
    lazyEq.pop(n)
    exprCache.pop(n)
    solverContext.pop(n)
    level -= n
  }

  override def flushStatistics(): Unit = {
    statListener.locator.writeStats("profile-rules.txt")
  }

  /**
    * Clean the context
    */
  override def dispose(): Unit = {
    flushStatistics()
    exprCache.dispose()
    intValueCache.dispose()
    intRangeCache.dispose()
    strValueCache.dispose()
    recordDomainCache.dispose()
    lazyEq.dispose()
    solverContext.dispose()
    profilerListener.foreach { _.dispose() }
  }


  /**
    * Add a text message to the storage.
    *
    * @param id      an id of the object, e.g., ArenaCell.id
    * @param message a text message
    */
  override def addMessage(id: Int, message: String): Unit = {
    messages += id -> message
  }

  /**
    * Find a message associated with the given id
    *
    * @param id an id of the object, e.g., ArenaCell.id
    * @return a text message, if exists
    * @throws NoSuchElementException if there is no message associated with the given id
    */
  override def findMessage(id: Int): String = {
    messages(id)
  }


  /**
    * Get the stack of expressions that is generated by the methods rewrite(.*)UntilDone.
    * This stack is non-empty only during the rewriting process.
    * Basically, it is only useful if the rewriter has thrown an exception.
    *
    * @return a list of TLA+ expressions
    */
  override def getRewritingStack(): Seq[TlaEx] = rewritingStack

  /**
    * Compute a key of a TLA+ expression to quickly decide on a short sequence of rules to try.
    *
    * @param ex a TLA+ expression
    * @return a string that gives us an equivalence class for similar operations (see the code)
    */
  private def key(ex: TlaEx): String = {
    ex match {
      // TODO: Is this correct?
      case OperEx(TlaOper.apply, NameEx(_), _*) =>
        "U@"

      case OperEx(oper, _*) =>
        "O@" + oper.name

      case LetInEx(_, _*) =>
        "L@"

      case ValEx(TlaInt(_)) =>
        "I@"

      case ValEx(TlaIntSet) =>
        "SI@"

      case ValEx(TlaNatSet) =>
        "SN@"

      case ValEx(TlaBool(_)) =>
        "B@"

      case ValEx(TlaBoolSet) =>
        "SB@"

      case NameEx(_) =>
        "N@"

      case _ =>
        "O@"
    }
  }
}
