package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaEx}

/**
 * Removes all primes from the affected expressions.
 *
 * @author
 *   Jure Kukovec
 */
class Deprime(tracker: TransformationTracker) extends TlaExTransformation {

  override def apply(ex: TlaEx): TlaEx = transform(ex)

  private def transform: TlaExTransformation = tracker.trackEx {
    case OperEx(TlaActionOper.prime, arg) =>
      transform(arg)

    case ex @ LetInEx(body, defs @ _*) =>
      // Transform bodies of all op.defs
      val newDefs = defs.map(tracker.trackOperDecl { d => d.copy(body = transform(d.body)) })
      val newBody = transform(body)
      if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)(ex.typeTag)

    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args.map(transform)
      if (args == newArgs) ex else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex => ex
  }
}
