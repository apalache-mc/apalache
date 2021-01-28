package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.transformations.{
  LanguageWatchdog,
  TlaExTransformation,
  TransformationTracker
}

class DeepCopy(tracker: TransformationTracker) extends TlaExTransformation {
  override def apply(expr: TlaEx): TlaEx = {
    transform(expr)
  }

  /**
    * Calls deep copy in a way that sets up tracking between every replacement (not just top-level)
    */
  def transform: TlaExTransformation = tracker.track {
    // LetInEx and OperEx are composite expressions
    case LetInEx(body, defs @ _*) =>
      // Transform bodies of all op.defs
      val newDefs = defs.map { x =>
        x.copy(
          body = transform(x.body)
        )
      }
      LetInEx(transform(body), newDefs: _*)

    case OperEx(op, args @ _*) =>
      OperEx(op, args map transform: _*)

    // terminal expressions, just copy
    case ex => ex.deepCopy()
  }
}

object DeepCopy {
  def apply(tracker: TransformationTracker): DeepCopy = {
    new DeepCopy(tracker)
  }
}
