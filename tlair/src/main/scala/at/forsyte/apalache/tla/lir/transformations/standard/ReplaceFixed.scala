package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.transformations.{
  TlaExTransformation,
  TransformationTracker
}

object ReplaceFixed {
  def replaceOne(
      replacedEx: TlaEx,
      newEx: => TlaEx, // takes a [=> TlaEx] to allow for the creation of new instances (with distinct UIDs)
      tracker: TransformationTracker
  ): TlaExTransformation = tracker.track { ex =>
    if (ex == replacedEx) newEx else ex
  }

  /**
    * Returns a transformation which replaces every instance of `replacedEx`
    * with an instance of `newEx`
    */
  def apply(
      replacedEx: TlaEx,
      newEx: => TlaEx, // takes a [=> TlaEx] to allow for the creation of new instances (with distinct UIDs)
      tracker: TransformationTracker
  ): TlaExTransformation = tracker.track { ex =>
    val tr = replaceOne(replacedEx, newEx, tracker)
    lazy val self = apply(replacedEx, newEx, tracker)
    ex match {
      case LetInEx(body, defs @ _*) =>
        // Transform bodies of all op.defs
        val newDefs = defs.map { x =>
          x.copy(
            body = self(x.body)
          )
        }
        val newBody = self(body)
        val retEx =
          if (defs == newDefs && body == newBody) ex
          else LetInEx(newBody, newDefs: _*)
        tr(retEx)

      case OperEx(op, args @ _*) =>
        val newArgs = args map self
        val retEx = if (args == newArgs) ex else OperEx(op, newArgs: _*)
        tr(retEx)

      case _ => tr(ex)
    }
  }

}
