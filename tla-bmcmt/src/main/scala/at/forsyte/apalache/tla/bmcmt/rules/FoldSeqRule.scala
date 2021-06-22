package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.InlinerOfUserOper
import at.forsyte.apalache.tla.lir._

/**
 * Rewriting rule for FoldSeq.
 * Unlike FoldSet, we do not need to consider overapproximations or exclude duplicate elements.
 *
 * @author Jure Kukovec
 */
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
      // getHas returns a sequence of start +: end +: cells
      // We drop start +: end, and just read the cells
      val seqCells = seqState.arena.getHas(seqCell).drop(2)

      // We start with the base value
      val initialState = seqState.setRex(baseCell.toNameEx)

      // we need the type signature
      val a = baseEx.typeTag.asTlaType1()
      val b = seqEx.typeTag.asTlaType1() match {
        case SeqT1(bType) => bType
        case nonSeq =>
          throw new TypingException(s"FoldSeq argument $seqEx should have the type Seq[b], found $nonSeq.")
      }
      val types = Map(
          "a" -> a,
          "b" -> b,
          "op" -> OperT1(Seq(a, b), a)
      )

      // expressions are transient, we don't need tracking
      val inliner = InlinerOfUserOper(BodyMapFactory.makeFromDecl(opDecl), new IdleTracker)

      // All that is left to do is folding, starting from initialState
      seqCells.foldLeft(initialState) { case (partialState, seqElemCell) =>
        // partialState currently holds the cell representing the previous application step
        val oldResultCellName = partialState.ex

        // newPartialResult = A(oldResultCellName, seqElemCell)
        val appEx = tla.appOp(tla.name(opDecl.name) ? "op", oldResultCellName ? "a", seqElemCell.toNameEx ? "b")
        val inlinedEx = inliner.apply(appEx.typed(types, "a"))
        val preInlineRewriteState = partialState.setRex(inlinedEx)
        // There is nothing left to do (no asserts), since the top value in the returned state will
        // hold the fully rewritten application (single cell)
        rewriter.rewriteUntilDone(preInlineRewriteState)
      }

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }
}
