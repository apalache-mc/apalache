package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.{OperEx, TlaUserOper}

/**
  * An operator application (for constant operators).
  *
  * @author Igor Konnov
  */
class UserOperRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(_: TlaUserOper, _*) => true

      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case OperEx(userOper: TlaUserOper, args @ _*) =>
      if (args.nonEmpty) {
        throw new RewriterException("Non-constant operators are not supported yet: " + state.ex)
      }

      val boundName = LetInRule.namePrefix + userOper.name
      if (!state.binding.contains(boundName)) {
        throw new RewriterException(s"Operator ${userOper.name} not found")
      }

      val finalState = state.setRex(state.binding(boundName).toNameEx)
      rewriter.coerce(finalState, state.theory)

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
  }
}
