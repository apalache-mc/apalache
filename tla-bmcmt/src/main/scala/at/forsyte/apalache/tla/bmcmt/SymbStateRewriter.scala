package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter.RewritingResult
import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, FreeExistentialsStore}
import at.forsyte.apalache.tla.bmcmt.caches.{ExprCache, IntValueCache, RecordDomainCache, StrValueCache}
import at.forsyte.apalache.tla.bmcmt.types.{CellT, TypeFinder}
import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A trait for a state rewriter. The main purpose of this trait is to rewrite a TLA+ expression
  * into a graph of cells. As a by-product, it produces SMT constraints on the graph.
  *
  * As this is the central point for the rewriting rules, it exposes many caches and storages.
  *
  * This trait implements StackableContext by delegating the respective operations to all the internal caches
  * and the SMT context. Thus, it is a central access point for context operations.
  *
  * @author Igor Konnov
  */
trait SymbStateRewriter extends StackableContext with MessageStorage {
  /**
    * A solver context that is populated by the rewriter.
    */
  def solverContext: SolverContext

  /**
    * Get the current context level, that is the difference between the number of pushes and pops made so far.
    *
    * @return the current level, always non-negative.
    */
  def contextLevel: Int

  /**
    * A type finder.
    * @return a type finder that can produce cell types
    */
  def typeFinder: TypeFinder[CellT]

  /**
    * The cache for lazy equalities, to avoid generating the same equality constraints many times.
    */
  def lazyEq: LazyEquality

  /**
    * A cache for integer literals.
    */
  def intValueCache: IntValueCache

  /**
    * A cache for string literals.
    */
  def strValueCache: StrValueCache

  /**
    * A cache of record domains.
    */
  def recordDomainCache: RecordDomainCache

  /**
    * An expression cache.
    */
  def exprCache: ExprCache

  /**
    * The store that marks free existential quantifiers. By default, empty.
    */
  def freeExistentialsStore: FreeExistentialsStore

  /**
    * The storage that associates with every expression id a grade, see ExprGrade.
    * @return
    */
  def exprGradeStore: ExprGradeStore

  /**
    * Rewrite a symbolic expression by applying at most one rewriting rule.
    *
    * @param state a symbolic state
    * @return the new symbolic state obtained by rewriting state
    */
  def rewriteOnce(state: SymbState): RewritingResult

  /**
    * Rewrite one expression until converged, or no rule applies.
    *
    * @param state a state to rewrite
    * @return the final state
    * @throws RewriterException if no rule applies
    */
  def rewriteUntilDone(state: SymbState): SymbState

  /**
    * Rewrite all expressions in a sequence.
    *
    * @param state a state to start with
    * @param es    a sequence of expressions to rewrite
    * @return a pair (the new state with the original expression, the rewritten expressions)
    */
  def rewriteSeqUntilDone(state: SymbState, es: Seq[TlaEx]): (SymbState, Seq[TlaEx])

  /**
    * An extended version of rewriteSeqUntilDone, where expressions are accompanied with bindings.
    *
    * @param state a state to start with
    * @param es    a sequence of expressions to rewrite accompanied with bindings
    * @return a pair (the old state in a new context, the rewritten expressions)
    */
  def rewriteBoundSeqUntilDone(state: SymbState, es: Seq[(Binding, TlaEx)]): (SymbState, Seq[TlaEx])

  /**
    * Coerce the state expression from the current theory to another theory.
    *
    * @param state        a symbolic state
    * @param targetTheory a target theory
    * @return a new symbolic state, if possible
    */
  def coerce(state: SymbState, targetTheory: Theory): SymbState
}


object SymbStateRewriter {
  sealed abstract class RewritingResult

  case class Done(symbState: SymbState) extends RewritingResult

  case class Continue(symbState: SymbState) extends RewritingResult

  case class NoRule() extends RewritingResult
}
