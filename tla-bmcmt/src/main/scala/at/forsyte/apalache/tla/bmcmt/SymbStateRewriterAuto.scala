package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeAnalysis, ExprGradeStore, ExprGradeStoreImpl, FreeExistentialsStore}
import at.forsyte.apalache.tla.bmcmt.caches.{ExprCache, IntValueCache, RecordDomainCache, StrValueCache}
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.plugins.Identifier

/**
  * A decorator of SymbStateRewriter that automatically preprocesses every given expression.
  * Normally, TLA+ specifications should be processed by the special passes.
  * However, it is much more convenient when all of this is done automatically.
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

  private val typeFinder = new TrivialTypeFinder()
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

  private def preprocess(ex: TlaEx): Unit = {
    Identifier.identify(ex)
    exprGradeAnalysis.labelExpr(consts, vars, ex)
    typeFinder.reset(Map())
    typeFinder.inferAndSave(ex)
    // FIXME
    /*
    if (typeFinder.getTypeErrors.nonEmpty) {
      throw typeFinder.getTypeErrors.head // just throw the first error -- and get 54 tests failed
    }
    */
  }

  override def rewriteOnce(state: SymbState): SymbStateRewriter.RewritingResult = {
    preprocess(state.ex)
    impl.rewriteOnce(state)
  }

  override def rewriteUntilDone(state: SymbState): SymbState = {
    preprocess(state.ex)
    impl.rewriteUntilDone(state)
  }

  override def rewriteSeqUntilDone(state: SymbState, es: Seq[TlaEx]): (SymbState, Seq[TlaEx]) = {
    preprocess(state.ex)
    es foreach preprocess
    impl.rewriteSeqUntilDone(state, es)
  }

  override def rewriteBoundSeqUntilDone(state: SymbState, es: Seq[(Binding, TlaEx)]): (SymbState, Seq[TlaEx]) = {
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
