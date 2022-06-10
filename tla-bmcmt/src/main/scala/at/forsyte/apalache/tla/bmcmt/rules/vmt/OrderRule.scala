package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans.{Neg, Or}
import at.forsyte.apalache.tla.lir.formulas.EUF.Equal
import at.forsyte.apalache.tla.lir.formulas.Ord.LtUninterpreted
import at.forsyte.apalache.tla.lir.formulas.Term
import at.forsyte.apalache.tla.lir.{ConstT1, IntT1, OperEx, TlaEx, Typed}
import at.forsyte.apalache.tla.lir.oper.{ApalacheInternalOper, TlaArithOper}

/**
 * OrderRule defines translations for partial/total order support in reTLA.
 *
 * This rule implements a special treatment of integers as a totally ordered sort without arithmetic, and should not be
 * used in combination with any integer-arithmetic rules (implemented in the future).
 *
 * @author
 *   Jure Kukovec
 */
class OrderRule(rewriter: ToTermRewriter) extends FormulaRule {
  override def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case OperEx(TlaArithOper.lt | TlaArithOper.gt | TlaArithOper.le | TlaArithOper.ge, _, _) => true
      case _                                                                                   => false
    }

  // Assume isApplicable
  override def apply(ex: TlaEx): Term = ex match {
    case OperEx(TlaArithOper.lt, lhs, rhs) =>
      LtUninterpreted(rewriter.rewrite(lhs), rewriter.rewrite(rhs))
    case OperEx(TlaArithOper.gt, lhs, rhs) =>
      // a > b ~~> b < a
      LtUninterpreted(rewriter.rewrite(rhs), rewriter.rewrite(lhs))
    case OperEx(TlaArithOper.le, lhs, rhs) =>
      val lRewrite = rewriter.rewrite(lhs)
      val rRewrite = rewriter.rewrite(rhs)
      // a <= b ~~> ~(b < a)
      Neg(LtUninterpreted(rRewrite, lRewrite))
    case OperEx(TlaArithOper.ge, lhs, rhs) =>
      val lRewrite = rewriter.rewrite(lhs)
      val rRewrite = rewriter.rewrite(rhs)
      // a >= b ~~> ~(a < b)
      Neg(LtUninterpreted(lRewrite, rRewrite))
    case _ => throw new RewriterException(s"PORule not applicable to $ex", ex)
  }
}
