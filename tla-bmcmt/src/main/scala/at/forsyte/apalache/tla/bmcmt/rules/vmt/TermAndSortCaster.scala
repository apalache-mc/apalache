package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.{FunctionSort, UninterpretedSort}
import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, FunT1, IntT1, StrT1, TlaEx, TlaType1, TupT1}
import at.forsyte.apalache.tla.lir.formulas.{Sort, StandardSorts, Term}

object TermAndSortCaster {

  def sortFromType(tt: TlaType1): Sort = tt match {
    case IntT1()                      => StandardSorts.IntSort()
    case BoolT1()                     => StandardSorts.BoolSort()
    case StrT1()                      => UninterpretedSort(tt.toString)
    case ConstT1(name)                => UninterpretedSort(name)
    case FunT1(TupT1(args @ _*), res) => FunctionSort(sortFromType(res), args map sortFromType: _*)
    case FunT1(arg, res)              => FunctionSort(sortFromType(res), sortFromType(arg))
    case _                            => throw new IllegalArgumentException(s"Type $tt not permitted in VMT")
  }

  def rewriteAndCast[T <: Term](rewriter: Rewriter, sortEval: Sort => Boolean)(ex: TlaEx): T = {
    val res = rewriter.rewrite(ex)
    val s = res.sort
    if (sortEval(s))
      res.asInstanceOf[T]
    else
      throw new RewriterException(s"Cannot cast sort of $res. Found: $s.", ex)
  }
  def rewriteAndCast[T <: Term](rewriter: Rewriter, sort: Sort)(ex: TlaEx): T =
    rewriteAndCast[T](rewriter, { s: Sort => s == sort })(ex)
}
