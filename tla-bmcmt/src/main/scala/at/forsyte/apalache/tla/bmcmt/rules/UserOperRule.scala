package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * An operator application (for constant operators).
  *
  * @author Igor Konnov
  */
class UserOperRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx( TlaOper.apply, NameEx(_), _* ) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case OperEx( TlaOper.apply, NameEx(operName), args @ _*) =>
      if (args.nonEmpty) {
        throw new RewriterException("Non-constant operators are not supported yet: " + state.ex, state.ex)
      }

      val boundName = LetInRule.namePrefix + operName
      if (!state.binding.contains(boundName)) {
        throw new RewriterException(s"Operator $operName not found", state.ex)
      }

      val finalState = state.setRex(state.binding(boundName).toNameEx)
      rewriter.coerce(finalState, state.theory)

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }
}
