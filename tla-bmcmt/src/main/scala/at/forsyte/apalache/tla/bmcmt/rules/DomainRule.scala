package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{FunT, RecordT, SeqT, TupleT}
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaFunOper

/**
  * Implements the rules: SE-DOM.
  *
  * @author Igor Konnov
  */
class DomainRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.domain, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.domain, funEx) =>
        val funState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(funEx))
        val funCell = funState.arena.findCellByNameEx(funState.ex)

        // no type information from the type finder is needed, as types are propagated in a straightforward manner
        funCell.cellType match {
          case FunT(_, _) | RecordT(_) | TupleT(_) | SeqT(_) => () // OK
          case _ =>
            throw new RewriterException("DOMAIN x where type(x) = %s is not implemented".format(funCell.cellType))
        }

        val dom = funState.arena.getDom(funCell)
        val finalState = funState.setRex(dom.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
