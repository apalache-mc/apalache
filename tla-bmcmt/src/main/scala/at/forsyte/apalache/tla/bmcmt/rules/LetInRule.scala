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
      case _: LetInEx => true
      case _          => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case LetInEx(body, defs @ _*) =>
      val boundState = defs.foldLeft(state)(bindOperator)
      val bodyState = rewriter.rewriteUntilDone(boundState.setRex(body))
      // forget the bindings that were introduced by let-definitions of this expression
      val newDefs =
        (bodyState.binding.toMap.keySet -- state.binding.toMap.keySet)
          .filter(_.startsWith(LetInRule.namePrefix))
      val finalBinding = Binding(bodyState.binding.toMap -- newDefs)
      bodyState.setBinding(finalBinding)

    case _ =>
      throw new RewriterException(
        "%s is not applicable".format(getClass.getSimpleName),
        state.ex
      )
  }

  private def bindOperator(state: SymbState, decl: TlaOperDecl): SymbState = {
    if (decl.formalParams.nonEmpty) {
      throw new RewriterException(
        "Found unexpanded %d-ary LET-IN %s. This is a preprocessing bug."
          .format(decl.formalParams.size, decl.name),
        state.ex
      )
    }

    val newState = rewriter.rewriteUntilDone(state.setRex(decl.body))
    val newCell = newState.arena.findCellByNameEx(newState.ex)
    val newBinding = Binding(
      newState.binding.toMap + (LetInRule.namePrefix + decl.name -> newCell)
    )
    newState.setBinding(newBinding)
  }
}
