package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.TlaInt

/**
  * Implements the rules: SE-INT-RANGE[1-2].
  *
  * @author Igor Konnov
   */
class IntDotDotRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaArithOper.dotdot, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaArithOper.dotdot, elems @ _*) =>
        if (elems.length != 2)
          throw new RewriterException("Expected two arguments to .., found " + elems.length)
        val (left: Int, right: Int) = getRange(elems)
        val range = Range(left, right + 1).map(i => ValEx(TlaInt(i)))
        val setCtor = OperEx(TlaSetOper.enumSet, range: _*)
        state.setRex(setCtor).setTheory(CellTheory())

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def getRange(elems: Seq[TlaEx]): (Int, Int) = {
    elems match {
      case Seq(ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
        if (!left.isValidInt || !right.isValidInt) {
          throw new RewriterException("Range bounds are too large to fit in scala.Int")
        }
        (left.toInt, right.toInt)

      case _ =>
        throw new RewriterException("Expected an integer range in .., found %s"
          .format(elems.map(UTFPrinter.apply).mkString("..")))
    }
  }
}
