package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.{RewriterException, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.bmcmt.caches.IntRangeCache
import at.forsyte.apalache.tla.bmcmt.types.FunT
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaFunOper

/**
 * Rewriting DOMAIN f, that is, translating the domain of a function, record, tuple, or sequence.
 *
 * @author
 *   Rodrigo Otoni
 */
class DomainRuleWithArrays(rewriter: SymbStateRewriter, intRangeCache: IntRangeCache)
    extends DomainRule(rewriter, intRangeCache) {

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.domain, funEx) =>
        val funState = rewriter.rewriteUntilDone(state.setRex(funEx))
        val funCell = funState.asCell

        funCell.cellType match {
          case FunT(_, _) =>
            val dom = funState.arena.getDom(funCell)
            funState.setRex(dom.toNameEx)

          case _ =>
            // TODO: consider records, tuples, and sequences in the arrays encoding
            super.apply(state)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
