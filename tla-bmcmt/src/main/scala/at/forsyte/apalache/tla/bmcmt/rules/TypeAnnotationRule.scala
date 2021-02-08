package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.BmcOper

/**
 * This rule just ignores a type annotation a <: b.
 * The actual use of type annotations happens at an earlier
 * type inference stage, see TrivialTypeFinder.
 *
 * @author Igor Konnov
 */
class TypeAnnotationRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(BmcOper.withType, _, _) => true
      case _                              => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(BmcOper.withType, ex, _) =>
        rewriter.rewriteUntilDone(state.setRex(ex))

      case e @ _ =>
        throw new RewriterException("%s is not applicable to %s".format(getClass.getSimpleName, e), state.ex)
    }
  }
}
