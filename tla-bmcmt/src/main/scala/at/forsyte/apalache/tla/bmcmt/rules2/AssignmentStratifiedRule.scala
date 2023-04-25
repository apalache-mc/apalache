package at.forsyte.apalache.tla.bmcmt.rules2

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaActionOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

class AssignmentStratifiedRule(rewriter: Rewriter) extends StratifiedRule[Unit] {

  override def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = ex match {
    case OperEx(ApalacheOper.assign, OperEx(TlaActionOper.prime, NameEx(name)), _) =>
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
