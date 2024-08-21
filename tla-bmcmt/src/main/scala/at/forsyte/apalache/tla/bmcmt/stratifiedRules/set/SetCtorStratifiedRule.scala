package at.forsyte.apalache.tla.bmcmt.stratifiedRules.set

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.{Rewriter, RewriterScope}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.{addCell, StratifiedRule}
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.{tlaU => tla}

/**
 * Rewrites the set constructor {e_1, ..., e_k}.
 *
 * @author
 *   Jure Kukovec
 */
class SetCtorStratifiedRule(rewriter: Rewriter) extends StratifiedRule[Unit] {

  def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = ex match {
    case OperEx(TlaSetOper.enumSet, _*) => true
    case _                              => false
  }

  def buildArena(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell, Unit) = ex match {
    case ex @ OperEx(TlaSetOper.enumSet, elems @ _*) =>
      // Rewrite the elements and remove the duplicate cells.
      // This does not guarantee us that all duplicates are removed,
      // as some cells may happen to be equal only in some models.

      val (scopeWithElems, newEs) =
        elems.foldLeft((startingScope, List.empty[ArenaCell])) { case ((scope, cellSeq), elem) =>
          val (newScope, elemCell) = rewriter.rewrite(elem)(scope)
          (newScope, cellSeq :+ elemCell)
        }

      val cells = newEs.distinct
      val setT = TlaType1.fromTypeTag(ex.typeTag)
      setT match {
        case SetT1(_) => ()
        case _        => throw new TypingException("Expected a finite set, found: " + setT, ex.ID)
      }
      val (newArena, newSetCell) = addCell(scopeWithElems.arena, setT)
      val newArenaWithHas = newArena.appendHas(newSetCell, cells.map(FixedElemPtr): _*)

      (scopeWithElems.copy(arena = newArenaWithHas), newSetCell, ())

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), ex)
  }

  def addConstraints(scope: RewriterScope, cell: ArenaCell, auxData: Unit): Unit =
    scope.arena.getHas(cell).foreach { ptr =>
      // by construction, ptr.toSmt should always eval to TRUE
      val memberEx: TlaEx = tla.eql(tla.in(ptr.elem.toBuilder, cell.toBuilder), ptr.toSmt)
      // consider optimizing to assert(tla.in(ptr.elem.toBuilder, cell.toBuilder)) ?
      // Z3 probably automatically turns x = true into x.
      rewriter.assert(memberEx)
    }

}
