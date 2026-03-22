package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, ProtoSeqOps}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.pp.Inliner

import scala.collection.immutable.SortedMap

/**
 * Rewriting rule for FoldSeq, which implements left-fold over sequences. Unlike FoldSet, we do not need to consider
 * overapproximations or exclude duplicate elements.
 *
 * @author
 *   Jure Kukovec, Igor Konnov
 */
class FoldSeqRule(rewriter: SymbStateRewriter, renaming: IncrementalRenaming) extends RewritingRule {
  private val picker = new CherryPick(rewriter)
  private val proto = new ProtoSeqOps(rewriter)

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
      var nextState = rewriter.rewriteUntilDone(state.setRex(baseEx))
      val baseCell = nextState.asCell

      // rewrite seqEx to its final cell form
      nextState = rewriter.rewriteUntilDone(nextState.setRex(seqEx))
      val seqCell = nextState.asCell
      val (protoSeq, len, _) = proto.unpackSeq(nextState.arena, seqCell)

      // the type of the operator application (the accumulator)
      val resultT = baseEx.typeTag.asTlaType1()
      // the type of the sequence elements
      val elemT = seqEx.typeTag.asTlaType1() match {
        case SeqT1(et) =>
          et

        case nonSeq =>
          throw new TypingException(s"FoldSeq argument $seqEx should have the type Seq[b], found $nonSeq.", ex.ID)
      }
      // the type of the folding operator
      val operT = OperT1(Seq(resultT, elemT), resultT)

      // expressions are transient, we don't need tracking
      val inliner = new Inliner(new IdleTracker, renaming)
      // We can make the scope directly, since InlinePass already ensures all is well.
      val seededScope: Inliner.Scope = SortedMap(opDecl.name -> opDecl)

      def binOp(state: SymbState, elem: ArenaCell): SymbState = {
        // the state holds the cell representing the accumulated result
        val prevResult = state.ex
        // newPartialResult = A(oldResultCellName, seqElemCell)
        val appEx = tla.appOp(tla.name(opDecl.name).as(operT), prevResult.as(resultT), elem.toNameEx.as(elemT))
        val inlinedEx = inliner.transform(seededScope)(appEx.as(resultT))
        // There is nothing left to do (no asserts), since the top value in the returned state will
        // hold the fully rewritten application (single cell)
        rewriter.rewriteUntilDone(state.setRex(inlinedEx))
      }

      // fold over the proto sequence
      proto.foldLeft(picker, nextState.setRex(baseCell.toNameEx), protoSeq, len, binOp)

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }
}
