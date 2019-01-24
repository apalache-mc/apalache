package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeAnalysis, ExprGradeStore, ExprGradeStoreImpl, FreeExistentialsStore}
import at.forsyte.apalache.tla.bmcmt.caches.{ExprCache, IntValueCache, RecordDomainCache, StrValueCache}
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.plugins.Identifier

/**
  * A decorator of SymbStateRewriter that automatically preprocesses every given expression.
  * Normally, TLA+ specifications should be processed by the special passes.
  * However, it is much more convenient when all of this is done automatically.
  * This class does a lot of preprocessing, so it is not meant to be efficient at all.
  * Use it only in the unit tests.
  *
  * @author Igor Konnov
  */
class SymbStateRewriterAuto(val solverContext: SolverContext) extends SymbStateRewriter {
  /**
    * The names that are treated as constants.
    */
  var consts: Set[String] = Set()
  /**
    * The names that are treated as (free) variables.
    */
  var vars: Set[String] = Set()

  val typeFinder = new TrivialTypeFinder()

  private val exprGradeStoreImpl = new ExprGradeStoreImpl()
  private val exprGradeAnalysis = new ExprGradeAnalysis(exprGradeStoreImpl)
  private val impl = new SymbStateRewriterImpl(solverContext, typeFinder, exprGradeStore)

  override def contextLevel: Int = impl.contextLevel

  override def lazyEq: LazyEquality = impl.lazyEq

  override def intValueCache: IntValueCache = impl.intValueCache

  override def strValueCache: StrValueCache = impl.strValueCache

  override def recordDomainCache: RecordDomainCache = impl.recordDomainCache

  override def exprCache: ExprCache = impl.exprCache

  override def freeExistentialsStore: FreeExistentialsStore = impl.freeExistentialsStore

  override def exprGradeStore: ExprGradeStore = exprGradeStoreImpl

  override var introFailures: Boolean = true

  private def reset(arena: Arena, binding: Binding): Unit = {
    def add(m: Map[String, CellT], c: ArenaCell) = m + (c.toString -> c.cellType)
    val cellTypes = arena.cellMap.values.foldLeft(Map[String, CellT]()) (add)
    def addName(m: Map[String, CellT], p: Tuple2[String, ArenaCell]) = m + (p._1 -> p._2.cellType)
    val cellAndBindingTypes = binding.foldLeft(cellTypes) (addName)
    // propagate cell types and bindings to the type inference engine
    typeFinder.reset(cellAndBindingTypes)
  }

  private def preprocess(ex: TlaEx): Unit = {
    Identifier.identify(ex)
    exprGradeAnalysis.labelExpr(consts, vars, ex)
    typeFinder.inferAndSave(ex)
    if (typeFinder.getTypeErrors.nonEmpty) {
      throw typeFinder.getTypeErrors.head // just throw the first error
    }
  }

  override def rewriteOnce(state: SymbState): SymbStateRewriter.RewritingResult = {
    reset(state.arena, state.binding)
    preprocess(state.ex)
    impl.rewriteOnce(state)
  }

  override def rewriteUntilDone(state: SymbState): SymbState = {
    reset(state.arena, state.binding)
    preprocess(state.ex)
    impl.rewriteUntilDone(state)
  }

  override def rewriteSeqUntilDone(state: SymbState, es: Seq[TlaEx]): (SymbState, Seq[TlaEx]) = {
    reset(state.arena, state.binding)
    preprocess(state.ex)
    es foreach preprocess
    impl.rewriteSeqUntilDone(state, es)
  }

  override def rewriteBoundSeqUntilDone(state: SymbState, es: Seq[(Binding, TlaEx)]): (SymbState, Seq[TlaEx]) = {
    reset(state.arena, state.binding)
    preprocess(state.ex)
    es.map(_._2).foreach(preprocess)
    impl.rewriteBoundSeqUntilDone(state, es)
  }

  override def coerce(state: SymbState, targetTheory: Theory): SymbState = {
    impl.coerce(state, targetTheory)
  }

  override def addMessage(id: Int, message: String): Unit = {
    impl.addMessage(id, message)
  }

  override def findMessage(id: Int): String = {
    impl.findMessage(id)
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
}
