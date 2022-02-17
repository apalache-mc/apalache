package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans.BoolExpr
import at.forsyte.apalache.tla.lir.formulas.EUF.{Equal, ITE}
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.BoolSort
import at.forsyte.apalache.tla.lir.formulas.Term
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaControlOper, TlaFunOper, TlaOper}

class EUFRule(rewriter: Rewriter) extends FormulaRule {

  private val eufOper: Set[TlaOper] = Set(
      TlaOper.eq,
      TlaOper.apply,
      TlaControlOper.ifThenElse,
      ApalacheOper.assign,
      TlaFunOper.funDef,
      TlaFunOper.app,
  )

  override def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case OperEx(oper, _*) => eufOper.contains(oper)
      case _                => false
    }

  // Assume isApplicable
  override def apply(ex: TlaEx): Term =
    ex match {
      case OperEx(TlaOper.eq | ApalacheOper.assign, lhs, rhs) =>
        // := is just = in VMT
        Equal(rewriter.rewrite(lhs), rewriter.rewrite(rhs))
      case OperEx(TlaOper.apply, fn, args @ _*) =>
        throw new RewriterException(s"Not implemented yet", ex)
      case OperEx(TlaControlOper.ifThenElse, ifEx, thenEx, elseEx) =>
        val castIfEx = TermCaster.rewriteAndCast[BoolExpr](rewriter, BoolSort())(ifEx)
        ITE(castIfEx, rewriter.rewrite(thenEx), rewriter.rewrite(elseEx))
//      case OperEx(TlaFunOper.funDef, ifEx, thenEx, elseEx) =>

      case _ => throw new RewriterException(s"BoolRule not applicable to $ex", ex)
    }
}
