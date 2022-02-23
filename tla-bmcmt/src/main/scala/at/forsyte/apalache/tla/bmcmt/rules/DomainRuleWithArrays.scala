package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.{RewriterException, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.bmcmt.caches.IntRangeCache
import at.forsyte.apalache.tla.bmcmt.types.{FunT, RecordT, SeqT, TupleT}
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

        // no type information from the type finder is needed, as types are propagated in a straightforward manner
        // TODO: consider records, tuples, and sequences in the arrays encoding
        funCell.cellType match {
          case RecordT(_) =>
            val dom = funState.arena.getDom(funCell)
            funState.setRex(dom.toNameEx)

          case TupleT(_) =>
            mkTupleDomain(funState, funCell)

          case SeqT(_) =>
            mkSeqDomain(funState, funCell)

          case FunT(_, _) =>
            val dom = funState.arena.getDom(funCell)
            funState.setRex(dom.toNameEx)

          case _ =>
            throw new RewriterException("DOMAIN x where type(x) = %s is not implemented".format(funCell.cellType),
                state.ex)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
