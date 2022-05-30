package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.PO.LtGeneric
import at.forsyte.apalache.tla.lir.formulas.Term
import at.forsyte.apalache.tla.lir.{ConstT1, OperEx, TlaEx, Typed}
import at.forsyte.apalache.tla.lir.oper.ApalacheInternalOper

/**
 * PORule defines translations for partial order support in reTLA.
 *
 * @author
 *   Jure Kukovec
 */
class PORule(rewriter: ToTermRewriter) extends FormulaRule {
  override def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case OperEx(ApalacheInternalOper.partialOrderLT, lhs, rhs) =>
        lhs.typeTag == rhs.typeTag &&
        (lhs.typeTag match {
          case Typed(_: ConstT1) => true
          case _                 => false
        })
        true
      case _ => false
    }

  // Assume isApplicable
  override def apply(ex: TlaEx): Term = ex match {
    case OperEx(ApalacheInternalOper.partialOrderLT, lhs, rhs) =>
      LtGeneric(rewriter.rewrite(lhs), rewriter.rewrite(rhs))
    case _ => throw new RewriterException(s"PORule not applicable to $ex", ex)
  }
}
