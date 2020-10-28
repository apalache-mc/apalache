package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.caches.{ExprCache, IntValueCache, RecordDomainCache, StrValueCache}
import at.forsyte.apalache.tla.bmcmt.rewriter.{RewriterConfig, SymbStateRewriterSnapshot}
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A decorator of SymbStateRewriter that automatically preprocesses every given expression.
  * Normally, TLA+ specifications should be processed by the special passes.
  * However, it is much more convenient when all of this is done automatically.
  * This class does a lot of preprocessing, so it is not meant to be efficient at all.
  * Use it only in the unit tests.
  *
  * @author Igor Konnov
  */
class SymbStateRewriterAuto(private var _solverContext: SolverContext) extends SymbStateRewriter {
  /**
    * The names that are treated as constants.
    */
  var consts: Set[String] = Set()
  /**
    * The names that are treated as (free) variables.
    */
  var vars: Set[String] = Set()

  var config: RewriterConfig = new RewriterConfig

  val typeFinder = new TrivialTypeFinder()


  /**
    * A solver context that is populated by the rewriter.
    */
  override def solverContext: SolverContext = _solverContext

  /**
    * Set the new solver context. Warning: the new context should be at the same stack depth as the rewriter.
    * Otherwise, pop may produce unexpected results.
    *
    * @param newContext new context
    */
  override def solverContext_=(newContext: SolverContext): Unit = {
    _solverContext = newContext
  }

  private val exprGradeStoreImpl = new ExprGradeStoreImpl()
  private val exprGradeAnalysis = new ExprGradeAnalysis(exprGradeStoreImpl)
  private val impl = new SymbStateRewriterImpl(solverContext, typeFinder, exprGradeStore)

  override def contextLevel: Int = impl.contextLevel

  override def lazyEq: LazyEquality = impl.lazyEq

  override def intValueCache: IntValueCache = impl.intValueCache

  override def strValueCache: StrValueCache = impl.strValueCache

  override def recordDomainCache: RecordDomainCache = impl.recordDomainCache

  override def exprCache: ExprCache = impl.exprCache

  override def formulaHintsStore: FormulaHintsStore = impl.formulaHintsStore

  override def exprGradeStore: ExprGradeStore = exprGradeStoreImpl

  private def reset(arena: Arena, binding: Binding): Unit = {
    def add(m: Map[String, CellT], c: ArenaCell) = m + (c.toString -> c.cellType)
    val cellTypes = arena.cellMap.values.foldLeft(Map[String, CellT]()) (add)
    def addName(m: Map[String, CellT], p: (String, ArenaCell)) = m + (p._1 -> p._2.cellType)
    val cellAndBindingTypes = binding.toMap.foldLeft(cellTypes) (addName)
    // propagate cell types and bindings to the type inference engine
    typeFinder.reset(cellAndBindingTypes)
  }

  private def preprocess(ex: TlaEx): Unit = {
    exprGradeAnalysis.labelExpr(consts, vars, ex)
    typeFinder.inferAndSave(ex)
    if (typeFinder.typeErrors.nonEmpty) {
      throw new TypeInferenceException(typeFinder.typeErrors)
    }
  }

  override def rewriteOnce(state: SymbState): SymbStateRewriter.RewritingResult = {
    reset(state.arena, state.binding)
    preprocess(state.ex)
    impl.rewriteOnce(state)
  }

  // TODO: rename to rewrite
  override def rewriteUntilDone(state: SymbState): SymbState = {
    reset(state.arena, state.binding)
    preprocess(state.ex)
    impl.rewriteUntilDone(state)
  }

  // TODO: rename to rewriteSeq
  override def rewriteSeqUntilDone(state: SymbState, es: Seq[TlaEx]): (SymbState, Seq[TlaEx]) = {
    reset(state.arena, state.binding)
    preprocess(state.ex)
    es foreach preprocess
    impl.rewriteSeqUntilDone(state, es)
  }

  // TODO: rename to rewriteSeqWithBindings
  override def rewriteBoundSeqUntilDone(state: SymbState, es: Seq[(Binding, TlaEx)]): (SymbState, Seq[TlaEx]) = {
    reset(state.arena, state.binding)
    preprocess(state.ex)
    es.map(_._2).foreach(preprocess)
    impl.rewriteBoundSeqUntilDone(state, es)
  }

  override def addMessage(id: Int, message: String): Unit = {
    impl.addMessage(id, message)
  }

  override def findMessage(id: Int): String = {
    impl.findMessage(id)
  }


  /**
    * Take a snapshot and return it
    *
    * @return the snapshot
    */
  override def snapshot(): SymbStateRewriterSnapshot = {
    impl.snapshot()
  }

  /**
    * Recover a previously saved snapshot (not necessarily saved by this object).
    *
    * @param shot a snapshot
    */
  override def recover(shot: SymbStateRewriterSnapshot): Unit = {
    impl.recover(shot)
  }

  override def push(): Unit = {
    impl.push()
  }

  override def pop(): Unit = {
    impl.pop()
  }

  override def pop(n: Int): Unit = {
    impl.pop(n)
  }

  override def dispose(): Unit = {
    impl.dispose()
  }

  /**
    * Flush collected statistics.
    */
  override def flushStatistics(): Unit = {
    impl.flushStatistics()
  }

  /**
    * Get the stack of expressions that is generated by the methods rewrite(.*)UntilDone.
    * This stack is non-empty only during the rewriting process.
    * Basically, it is only useful if the rewriter has thrown an exception.
    *
    * @return a list of TLA+ expressions
    */
  override def getRewritingStack(): Seq[TlaEx] = impl.getRewritingStack()
}
