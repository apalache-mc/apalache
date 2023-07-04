package at.forsyte.apalache.tla.bmcmt.stratifiedRules.set

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux.{Rewriter, RewriterScope}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.{addCell, StratifiedRule}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

/**
 * Rewrites a set comprehension { x \in S: P }.
 *
 * @author
 *   Jure Kukovec
 */
class SetFilterStratifiedRule(rewriter: Rewriter) extends StratifiedRule[Unit] {

  override def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = ex match {
    case OperEx(TlaSetOper.filter, _*) => true
    case _                             => false
  }

  def buildArena(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell, Unit) = ex match {
    case ex @ OperEx(TlaSetOper.filter, NameEx(varName), setEx, predEx) =>
      // rewrite the set expression into a memory cell
      TlaType1.fromTypeTag(setEx.typeTag) match {
        case SetT1(_) => ()
        case tp @ _   => throw new NotImplementedError("A set filter over %s is not implemented".format(tp))
      }
      val (postSetScope, setCell) = rewriter.rewrite(setEx)(startingScope)

      // unfold the set and produce boolean constants for every potential element
      val potentialCellPtrs = postSetScope.arena.getHas(setCell)
      // similar to SymbStateRewriter.rewriteSeqUntilDone, but also handling exceptions

      def rewritePredExWithBinding(ptr: ElemPtr): TBuilderInstruction = {
        // add [cell/x]
        val newBinding = Binding(postSetScope.binding.toMap + (varName -> ptr.elem))
        rewriter.rewrite(predEx)(postSetScope.copy(binding = newBinding))._2.toBuilder
      }

      // At this point, we force all pointers to SmtExprElemPtr
      val filteredPtrsAndPreds = potentialCellPtrs.map { ptr =>
        val pred = rewritePredExWithBinding(ptr)
        (ptr.restrict(pred), pred)
      }

      // get the result type from the type finder
      val resultType = TlaType1.fromTypeTag(ex.typeTag)
      assert(resultType.isInstanceOf[SetT1])

      // introduce a new set
      val (newArena, newSetCell) = addCell(postSetScope.arena, resultType)
      val newArenaWithHas = newArena.appendHas(newSetCell, filteredPtrsAndPreds.map(_._1): _*)

      (postSetScope.copy(arena = newArenaWithHas), newSetCell, ())
    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), ex)
  }

  override def addConstraints(scope: RewriterScope, cell: ArenaCell, auxData: Unit): Unit =
    scope.arena.getHas(cell).foreach { ptr =>
      val memberEx: TlaEx = tla.eql(tla.in(ptr.elem.toBuilder, cell.toBuilder), ptr.toSmt)
      rewriter.assert(memberEx)
    }

}
