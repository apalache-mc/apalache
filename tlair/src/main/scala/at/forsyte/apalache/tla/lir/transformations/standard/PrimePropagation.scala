package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
  * This is a simple reference implementation of an expression transformer. It expands the prime operator,
  * that is, when it meets an expression e', it propagates primes inside e.
  *
  * @param tracker a transformation tracker
  */
class PrimePropagation(tracker: TransformationTracker) extends TlaExTransformation {
  override def apply(e: TlaEx): TlaEx = transform(primed = false)(e)

  private def transform(primed: Boolean): TlaEx => TlaEx = tracker.track {
    case OperEx(TlaActionOper.prime, e) =>
      transform(primed)(e)

    case OperEx(oper, args @ _*) =>
      OperEx(oper, args map transform(primed) :_*)

    // TODO: ENABLED and module instances need a special treatment

    case ne @ NameEx(name) =>
      if (primed) OperEx(TlaActionOper.prime, ne) else ne

    case e => e
  }

}
