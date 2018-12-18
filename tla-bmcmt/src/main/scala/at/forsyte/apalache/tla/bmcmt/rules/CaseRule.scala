package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}


/**
  * A rule for case. Similar to TLC, CASE is translated into a chain of IF-THEN-ELSE expressions.
  *
  * @author Igor Konnov
  */
class CaseRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaControlOper.caseWithOther, _*) => true
      case OperEx(TlaControlOper.caseNoOther, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    def decorateWithIf(elseEx: TlaEx, guardAction: Tuple2[TlaEx, TlaEx]): OperEx = {
      tla.ite(guardAction._1, guardAction._2, elseEx)
    }

    state.ex match {
      case OperEx(TlaControlOper.caseWithOther, otherEx, args @ _*) =>
        // similar to TLC, translate into the chain of IF-THEN-ELSE
        val revGuardsAndActions = mkGuardsAndActions(args)
        val iteWaterfall = revGuardsAndActions.foldLeft(otherEx)(decorateWithIf)
        val finalState = rewriter.rewriteUntilDone(state.setRex(iteWaterfall))
        rewriter.coerce(finalState, state.theory)

      case OperEx(TlaControlOper.caseNoOther, args @ _*) =>
        // similar to TLC, translate into the chain of IF-THEN-ELSE
        val revGuardsAndActions = mkGuardsAndActions(args)
        // First, rewrite the last action, to infer the type of the OTHER case, which we need in any case.
        // This code is annoying, as we do not have a separate phase for type inference yet...
        val lastState = rewriter.rewriteUntilDone(state.setRex(revGuardsAndActions.head._2).setTheory(CellTheory()))
        val lastType = getCellType(lastState)
        val assertState = new TypedAssert(rewriter)
          .typedAssert(lastState, lastType, tla.bool(false),
            "It may happen that no guard in CASE is applicable")
        val lastOrAssert = tla.ite(revGuardsAndActions.head._1, lastState.ex, assertState.ex)
        // the rest is easy: just create a chain of IF-THEN-ELSE expressions
        val iteWaterfall = revGuardsAndActions.tail.foldLeft(lastOrAssert)(decorateWithIf)
        val finalState = rewriter.rewriteUntilDone(assertState.setRex(iteWaterfall))
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def mkGuardsAndActions(args: Seq[TlaEx]): Seq[Tuple2[TlaEx, TlaEx]] = {
    assert(args.length % 2 == 0) // even
    val guards = args.zipWithIndex.filter(p => p._2 % 2 == 0).map(_._1)
    val actions = args.zipWithIndex.filter(p => p._2 % 2 != 0).map(_._1)
    guards.zip(actions).reverse
  }

  private def getCellType(state: SymbState): CellT = {
    state.ex match {
      case NameEx(name) => state.arena.findCellByName(name).cellType
      case _ =>
        throw new RewriterException("The rewriting result is not a cell but %s" + state.ex)
    }
  }

}
