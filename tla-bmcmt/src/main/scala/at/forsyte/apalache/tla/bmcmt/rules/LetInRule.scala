package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.{LetInEx, TlaOperDecl}

object LetInRule {
  val namePrefix = "Oper:"
}

/**
  * A simple translation of LET ... IN that supports only nullary operators.
  *
  * @author Igor Konnov
  */
class LetInRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case _ : LetInEx => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case LetInEx( body, defs@_* ) =>
      val boundState = defs.foldLeft(state) (bindOperator)
      val bodyState = rewriter.rewriteUntilDone(boundState.setTheory(state.theory).setRex(body))
      val finalState = bodyState.setBinding(state.binding) // recover the original binding
      rewriter.coerce(finalState, state.theory)
    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
  }

  private def bindOperator(state: SymbState, decl: TlaOperDecl): SymbState = {
    if (decl.formalParams.nonEmpty) {
      throw new RewriterException("Non-constant operators in LET-IN are not supported yet: " + decl)
    }

    val newState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(decl.body))
    val newCell = newState.arena.findCellByNameEx(newState.ex)
    val newBinding = newState.binding + (LetInRule.namePrefix + decl.name -> newCell)
    newState.setBinding(newBinding)
  }
}
