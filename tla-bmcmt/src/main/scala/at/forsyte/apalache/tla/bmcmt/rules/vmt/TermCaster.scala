package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.formulas.{Sort, Term}

object TermCaster {
  def rewriteAndCast[T <: Term](rewriter: Rewriter, sort: Sort)(ex: TlaEx): T = {
    val res = rewriter.rewrite(ex)
    res.sort match {
      case `sort` => res.asInstanceOf[T]
      case s      => throw new RewriterException(s"Expected sort of $res to be $sort, found: $s", ex)
    }
  }
}
