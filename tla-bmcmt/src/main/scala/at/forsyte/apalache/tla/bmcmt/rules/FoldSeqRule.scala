package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.InlinerOfUserOper
import at.forsyte.apalache.tla.lir._

class FoldSeqRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(ApalacheOper.foldSeq, LetInEx(NameEx(appName), TlaOperDecl(operName, params, _)), _, _) =>
        appName == operName && params.size == 2
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    // assume isApplicable
    case ex @ OperEx(ApalacheOper.foldSeq, LetInEx(NameEx(_), opDecl), baseEx, seqEx) =>
      // rewrite baseEx to its final cell form
      val baseState = rewriter.rewriteUntilDone(state.setRex(baseEx))
      val baseCell = baseState.asCell

      // rewrite seqEx to its final cell form
      val seqState = rewriter.rewriteUntilDone(baseState.setRex(seqEx))
      val seqCell = seqState.asCell

      // Assume that seqCell is in fact a Seq-type cell
      val seqCells = seqState.arena.getHas(seqCell).drop(2) // drop start, end

      val initialState = seqState.setRex(baseCell.toNameEx)
      val foldResultType = baseCell.cellType

      // expressions are transient, we don't need tracking
      val inliner = InlinerOfUserOper(BodyMapFactory.makeFromDecl(opDecl), new IdleTracker)

      val ret = seqCells.foldLeft(initialState) { case (partialState, seqElemCell) =>
        val oldResultName = partialState.ex
        val arenaWithNewPartial = partialState.arena.appendCell(foldResultType)
        val newPartialResultCell = arenaWithNewPartial.topCell

        // newPartialResult = A(oldPartialResult, seqElemCell)
        val appEx = tla.appDecl(opDecl, oldResultName, seqElemCell.toNameEx)
        val inlinedEx = inliner.apply(appEx)
        // We now rewrite A(old, hd) to a cell
        val preInlineRewriteState = partialState.setArena(arenaWithNewPartial).setRex(inlinedEx)
        val postInlineRewriteState = rewriter.rewriteUntilDone(preInlineRewriteState)
        val inlinedAppEx = postInlineRewriteState.ex

        // We assert the condition implying the new value
        solverAssert(tla.eql(newPartialResultCell.toNameEx, inlinedAppEx))
        postInlineRewriteState.setRex(newPartialResultCell.toNameEx)
      }
      ret

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }

  // convenience shorthand
  def solverAssert: TlaEx => Unit = rewriter.solverContext.assertGroundExpr
}
