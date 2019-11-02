package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{LetInEx, NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations._

/**
  * Replace every equality x' = e with x' \in {e}. This transformation is needed by the assignment solver,
  * so we extracted it into an optional transformation.
  */
class PrimedEqualityToMembership(tracker: TransformationTracker) extends TlaExTransformation {
  override def apply(ex: TlaEx): TlaEx = {
    transform(ex)
  }

  def transform: TlaExTransformation = tracker.track {
    // interesting case
    case OperEx(TlaOper.eq, lhs@OperEx(TlaActionOper.prime, NameEx(name)), rhs) =>
      OperEx(TlaSetOper.in, lhs, OperEx(TlaSetOper.enumSet, rhs))

    // standard recursive processing of composite operators and let-in definitions
    case ex@LetInEx(body, defs@_*) =>
      // Transform bodies of all op.defs
      val newDefs = defs.map { x =>
        x.copy(body = transform(x.body))
      }
      val newBody = transform(body)
      if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)

    case ex@OperEx(op, args@_*) =>
      val newArgs = args map transform
      if (args == newArgs) ex else OperEx(op, newArgs: _*)

    case ex => ex
  }
}

object PrimedEqualityToMembership {
  def apply(tracker: TransformationTracker): PrimedEqualityToMembership = {
    new PrimedEqualityToMembership(tracker)
  }
}