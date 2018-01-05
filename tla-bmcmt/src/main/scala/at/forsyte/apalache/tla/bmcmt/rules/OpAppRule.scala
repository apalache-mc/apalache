package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.{RewriterException, RewritingRule, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * An operator application (for constant operators).
  *
  * @author Igor Konnov
  */
class OpAppRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaOper.apply, _*) => true

      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case OperEx(TlaOper.apply, NameEx(opName), args @ _*) =>
      if (args.nonEmpty) {
        throw new RewriterException("Non-constant operators are not supported yet: " + state.ex)
      }

      val boundName = LetInRule.namePrefix + opName
      if (!state.binding.contains(boundName)) {
        throw new RewriterException(s"Operator $opName not found")
      }

      val finalState = state.setRex(state.binding(boundName).toNameEx)
      rewriter.coerce(finalState, state.theory)
  }
}
