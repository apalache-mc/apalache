package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans.BoolExpr
import at.forsyte.apalache.tla.lir.formulas.EUF.{Apply, Equal}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaControlOper, TlaOper}

class EUFRule(rewriter: Rewriter) extends FormulaRule {
  override def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case OperEx(TlaOper.eq | TlaOper.apply | TlaControlOper.ifThenElse, _*) => true
      // := is just = in VMT
      case OperEx(ApalacheOper.assign, _*) => true
      case _                               => false
    }

  // Assume isApplicable
  override def apply(ex: TlaEx): BoolExpr =
    ex match {
      case OperEx(TlaOper.eq, lhs, rhs)          => Equal(rewriter.rewrite(lhs), rewriter.rewrite(rhs))
      case OperEx(ApalacheOper.assign, lhs, rhs) => Equal(rewriter.rewrite(lhs), rewriter.rewrite(rhs))
      case OperEx(TlaOper.apply, fn, args @ _*)  => throw new RewriterException(s"Not implemented yet", ex)
      case OperEx(TlaControlOper.ifThenElse, ifEx, thenEx, elseEx) =>
        throw new RewriterException(s"Not implemented yet", ex)
      case _ => throw new RewriterException(s"BoolRule not applicable to $ex", ex)
    }
}
