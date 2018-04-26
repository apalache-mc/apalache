package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.convenience._


/**
  * A rule for case. For the moment, we only have a workaround for CASE p -> A [] OTHER -> B, which is translated
  * to IF p THEN A ELSE B. We introduced the rule to cope with the provisional version of the assignment solver
  * that translates IF-THEN-ELSE to case.
  *
  * TODO: implement translation for the general case.
  *
  * @author Igor Konnov
  */
class CaseRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaControlOper.caseWithOther, _, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaControlOper.caseWithOther, otherEx, predEx, actionEx) =>
        // simply translate it to IF-THEN-ELSE
        state.setRex(tla.ite(predEx, actionEx, otherEx))

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
