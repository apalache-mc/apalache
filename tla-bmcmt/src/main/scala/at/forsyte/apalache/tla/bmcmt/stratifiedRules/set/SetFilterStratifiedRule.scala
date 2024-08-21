package at.forsyte.apalache.tla.bmcmt.stratifiedRules.set

import at.forsyte.apalache.tla.bmcmt.{RewriterException, _}
import at.forsyte.apalache.tla.bmcmt.stratifiedRules.{addCell, Rewriter, RewriterScope, StratifiedRule}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.values.{TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.types.{tlaU => tla}

/**
 * Rewrites a set comprehension { x \in S: P }.
 *
 * @author
 *   Jure Kukovec
 */
class SetFilterStratifiedRule(rewriter: Rewriter) extends StratifiedRule[Unit] {

  override def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = ex match {
    case OperEx(TlaSetOper.filter, NameEx(_), set, _) =>
      set match {
        // We specifically exclude Infinite sets, which may not be filtered over.
        case ValEx(TlaIntSet | TlaNatSet) => false
        case _                            => true
      }
    case _ => false
  }

  def buildArena(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell, Unit) = ex match {
    case OperEx(TlaSetOper.filter, NameEx(varName), setEx, predEx) =>
      // Throw an error if attempting to filter Int/Nat
      setEx match {
        case ValEx(TlaIntSet | TlaNatSet) =>
          throw new RewriterException(s"A set filter over an infinite set ($setEx) is not supported.", ex)
        case _ => ()
      }

      // rewrite the set expression into a cell
      val (postSetScope, setCell) = rewriter.rewrite(setEx)(startingScope)

      // The overapproximation for a filtered set is the original set.
      val potentialCellPtrs = postSetScope.arena.getHas(setCell)

      // What remains is to correctly constrain the pointers
      // At this point, we force all pointers to SmtExprElemPtr via _.restrict
      val restrictedPtrs = potentialCellPtrs.map { ptr =>
        // add [cell/x]
        val newBinding = Binding(postSetScope.binding.toMap + (varName -> ptr.elem))
        val pred = rewriter.rewrite(predEx)(postSetScope.copy(binding = newBinding))._2.toBuilder
        ptr.restrict(pred)
      }

      // get the result type from the type finder
      val resultType = TlaType1.fromTypeTag(setEx.typeTag)
      require(resultType.isInstanceOf[SetT1], "Set filter may only be applied to Set[_]-typed values.")

      // introduce a new set
      val (newArena, newSetCell) = addCell(postSetScope.arena, resultType)
      val newArenaWithHas = newArena.appendHas(newSetCell, restrictedPtrs: _*)

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
