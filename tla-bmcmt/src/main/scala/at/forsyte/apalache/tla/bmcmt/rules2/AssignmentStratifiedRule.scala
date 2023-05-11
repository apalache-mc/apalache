package at.forsyte.apalache.tla.bmcmt.rules2

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaActionOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
 * Implements the assignment rule. Similar to TLC, this is a special form of x' \in S operator that is treated as an
 * assignment of a value from S to the variable x'.
 *
 * Since version 0.6.x, most of the work is delegated to existential quantification, that is, assignments are treated as
 * \E t \in S: x' = t
 *
 * @author
 *   Jure Kukovec
 */
class AssignmentStratifiedRule(rewriter: Rewriter) extends StratifiedRule[Unit] {

  override def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = ex match {
    case OperEx(ApalacheOper.assign, OperEx(TlaActionOper.prime, NameEx(name)), _) =>
      // The variable must be unbound, and have a legal variable name, i.e. not a cell name
      !ArenaCell.isValidName(name) && !scope.binding.contains(name + "'")
    case _ => false
  }

  def buildArena(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell, Unit) = ex match {
    case OperEx(ApalacheOper.assign, OperEx(TlaActionOper.prime, NameEx(name)), rhs) =>
      val (postRhsScope, rhsCell) = rewriter.rewrite(rhs)(startingScope)
      val newBinding = Binding(postRhsScope.binding.toMap + (name + "'" -> rhsCell))
      (postRhsScope.copy(binding = newBinding), PureArena.cellTrue(postRhsScope.arena), ())

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), ex)
  }

  def addConstraints(scope: RewriterScope, cell: ArenaCell, auxData: Unit): Unit = ()
}
