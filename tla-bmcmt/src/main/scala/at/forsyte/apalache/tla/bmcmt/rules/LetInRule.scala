package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.{LetInEx, TlaOperDecl}

object LetInRule {
  val namePrefix = "LetDef:"
}

/**
  * A simple translation of LET ... IN that supports only the operators without arguments.
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
      // forget the bindings that were introduced by let-definitions of this expression
      val newDefs = (bodyState.binding.keySet -- state.binding.keySet).filter(_.startsWith(LetInRule.namePrefix))
      val finalBinding = bodyState.binding -- newDefs
      val finalState = bodyState.setBinding(finalBinding)
      rewriter.coerce(finalState, state.theory)
    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }

  private def bindOperator(state: SymbState, decl: TlaOperDecl): SymbState = {
    if (decl.formalParams.nonEmpty) {
      throw new RewriterException("Found unexpanded %d-ary LET-IN %s. This is a preprocessing bug."
        .format(decl.formalParams.size, decl.name), state.ex)
    }

    val newState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(decl.body))
    val newCell = newState.arena.findCellByNameEx(newState.ex)
    val newBinding = newState.binding + (LetInRule.namePrefix + decl.name -> newCell)
    newState.setBinding(newBinding)
  }
}
