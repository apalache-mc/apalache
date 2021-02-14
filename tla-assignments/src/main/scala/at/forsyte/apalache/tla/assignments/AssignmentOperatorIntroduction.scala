package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.oper.{BmcOper, TlaActionOper, TlaOper}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
 * <p> Replaces ass assignment candidates of the form x' = e, which satisfy the predicate `isAssignment`,
 * into a special assignment form, x' <- e, for optimization purposes. </p>
 */
class AssignmentOperatorIntroduction(
    isAssignment: UID => Boolean, tracker: TransformationTracker
) extends TlaExTransformation {
  private var uidReplacementMap: Map[UID, UID] = Map.empty

  override def apply(expr: TlaEx): TlaEx = {
    transform(expr)
  }

  def transform: TlaExTransformation = tracker.trackEx {
    case ex @ OperEx(TlaOper.eq, prime @ OperEx(TlaActionOper.prime, _: NameEx), asgnVal) if isAssignment(ex.ID) =>
      val ret = OperEx(BmcOper.assign, prime, asgnVal)
      uidReplacementMap += ex.ID -> ret.ID
      ret
    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map transform
      if (args == newArgs) ex else OperEx(op, newArgs: _*)
    case ex @ LetInEx(body, defs @ _*) =>
      val newDefs = defs.map { x => x.copy(body = transform(x.body)) }
      val newBody = transform(body)
      if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)
    case ex => ex
  }

  def getReplacements: Map[UID, UID] = uidReplacementMap
}

object AssignmentOperatorIntroduction {
  def predicateFromSet(set: Set[UID]): UID => Boolean = set.contains

  def apply(isAssignment: UID => Boolean, tracker: TransformationTracker): AssignmentOperatorIntroduction =
    new AssignmentOperatorIntroduction(isAssignment, tracker)

  def apply(assignments: Set[UID], tracker: TransformationTracker): AssignmentOperatorIntroduction =
    new AssignmentOperatorIntroduction(predicateFromSet(assignments), tracker)
}
