package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.caches.IntRangeCache
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.io.UTFPrinter
import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import at.forsyte.apalache.tla.lir.values.TlaInt

/**
 * Rewrites an integer range a..b.
 *
 * @author Igor Konnov
 */
class IntDotDotRule(rewriter: SymbStateRewriter, intRangeCache: IntRangeCache) extends RewritingRule {
  private def simplifier = new ConstSimplifierForSmt()

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaArithOper.dotdot, _*) => true
      case _                               => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaArithOper.dotdot, elems @ _*) =>
        if (elems.length != 2)
          throw new RewriterException("Expected two arguments to .., found " + elems.length, state.ex)
        val (start: Int, endInclusive: Int) = getRange(state.ex, elems)
        val (newArena, rangeCell) = intRangeCache.create(state.arena, (start, endInclusive))
        state.setArena(newArena).setRex(rangeCell.toNameEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def getRange(ex: TlaEx, elems: Seq[TlaEx]): (Int, Int) = {
    // Do a shallow simplification. The expression optimizer pass should have done a deep one.
    elems map (simplifier.simplifyShallow(_)) match {
      case Seq(ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
        if (!left.isValidInt || !right.isValidInt) {
          throw new RewriterException("Range bounds are too large to fit in scala.Int", ex)
        }
        (left.toInt, right.toInt)

      case _ =>
        throw new RewriterException(
            "Expected a constant integer range in .., found %s"
              .format(elems.map(UTFPrinter.apply).mkString("..")), ex)
    }
  }
}
