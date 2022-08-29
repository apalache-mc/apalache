package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.{RewriterException, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.bmcmt.caches.IntRangeCache
import at.forsyte.apalache.tla.bmcmt.types.CellTFrom
import at.forsyte.apalache.tla.lir.{FunT1, OperEx, RecRowT1, RecT1, SeqT1, TupT1}
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

        // TODO: consider records, tuples, and sequences in the arrays encoding
        funCell.cellType match {
          case CellTFrom(RecT1(_)) =>
            val dom = funState.arena.getDom(funCell)
            funState.setRex(dom.toNameEx)

          case CellTFrom(RecRowT1(_)) =>
            recordOps.domain(funState, funCell)

          case CellTFrom(tt @ TupT1(_ @_*)) =>
            mkTupleDomain(funState, tt)

          case CellTFrom(SeqT1(_)) =>
            mkSeqDomain(funState, funCell)

          case CellTFrom(FunT1(_, _)) =>
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
