package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{InfSetT, PowSetT}
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.pp.TlaInputError

/**
 * Rewrites the powerset SUBSET S for a set S.
 *
 * @author
 *   Igor Konnov
 */
class PowSetCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.powerset, _) => true
      case _                              => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.powerset, setEx) =>
        // switch to cell theory
        var nextState = rewriter.rewriteUntilDone(state.setRex(setEx))

        val dom = nextState.arena.findCellByNameEx(nextState.ex)
        // SUBSET of an infinite set (e.g. SUBSET Int, SUBSET Nat) is unsupported: every
        // downstream rule that iterates the arena cells of the base set (PowSetCtor
        // expansion, pickFromPowset, etc.) silently treats Int/Nat as if they had no
        // elements, which leads to the powerset being mis-represented as a singleton
        // containing only the empty subset.  In the wider context of records and
        // record-typed sets this manifests as a confusing checker crash, see #2972.
        // Reject up-front with an actionable message instead.
        dom.cellType match {
          case InfSetT(_) =>
            throw new TlaInputError(
                s"SUBSET of an infinite set (${dom.cellType}) is not supported. " +
                  s"Replace the base set with a finite one, e.g. SUBSET (a..b).",
                Some(state.ex.ID),
            )
          case _ => () // ok
        }
        nextState = nextState.updateArena(_.appendCellOld(PowSetT(dom.cellType.toTlaType1)))
        val powSetCell = nextState.arena.topCell
        nextState = nextState.updateArena(_.setDom(powSetCell, dom))
        nextState.setRex(powSetCell.toNameEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
