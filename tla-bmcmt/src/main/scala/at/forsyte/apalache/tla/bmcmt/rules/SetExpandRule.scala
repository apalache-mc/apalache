package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.PowSetCtor
import at.forsyte.apalache.tla.bmcmt.types.InfSetT
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaSetOper}
import at.forsyte.apalache.tla.pp.TlaInputError
import com.typesafe.scalalogging.LazyLogging

/**
 * This rule expands a powerset, that is, SUBSET S for a set S. In the future, it might also expand a set of functions,
 * that is, [S -> T], but this does not seem to be practical.
 *
 * @author
 *   Igor Konnov
 */
class SetExpandRule(rewriter: SymbStateRewriter) extends RewritingRule with LazyLogging {
  // the minimal cardinality of a base set that should trigger a warning
  private val BASESET_WARNING_THRESHOLD = 10

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(ApalacheOper.expand, OperEx(TlaSetOper.powerset, _))  => true
      case OperEx(ApalacheOper.expand, OperEx(TlaSetOper.funSet, _, _)) => true
      case _                                                            => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(ApalacheOper.expand, OperEx(TlaSetOper.funSet, _, _)) =>
        throw new RewriterException("Trying to expand a set of functions. This will blow up the solver.", ex)

      case OperEx(ApalacheOper.expand, OperEx(TlaSetOper.powerset, basesetEx)) =>
        val nextState = rewriter.rewriteUntilDone(state.setRex(basesetEx))
        val baseset = nextState.asCell
        // SUBSET of an infinite set (e.g. SUBSET Int, SUBSET Nat) is unsupported.  The
        // arena cell for an infinite set has an empty `has` relation, so the powerset
        // expansion below would silently produce a singleton containing only the empty
        // subset.  Downstream rules then compare a CellTFrom(SetT1(_)) cell against an
        // InfSetT(_) cell, which manifests either as a confusing checker crash
        // ("Unexpected equality test over types ...") or as a spurious deadlock, see
        // #2972.  Reject up-front with an actionable message instead.
        baseset.cellType match {
          case InfSetT(_) =>
            throw new TlaInputError(
                s"SUBSET of an infinite set (${baseset.cellType}) is not supported. " +
                  s"Replace the base set with a finite one, e.g. SUBSET (a..b).",
                Some(state.ex.ID),
            )
          case _ => () // ok
        }
        val baseSize = nextState.arena.getHas(baseset).length
        if (baseSize >= BASESET_WARNING_THRESHOLD) {
          val msg =
            s"The set $baseset is expanded, producing O(2^$baseSize) constraints. This may slow down the solver."
          logger.warn(msg)
        }
        new PowSetCtor(rewriter).confringo(nextState, nextState.asCell)

      case e @ _ =>
        throw new RewriterException("%s is not applicable to %s".format(getClass.getSimpleName, e), state.ex)
    }
  }
}
