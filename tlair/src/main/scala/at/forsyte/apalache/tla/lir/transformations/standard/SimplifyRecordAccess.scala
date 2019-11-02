package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.TlaStr

/**
  * A simplifier that replaces record access to an explicitly constructed record with the known value,
  * e.g., {a |-> 1, b |-> 2}.b is rewritten into 2.
  *
  * TODO: this transformation should be part of a more general constant simplifier, see how it is done in Keramelizer.
  *
  * @param tracker a transformation tracker
  *
  * @author Jure Kukovec, Igor Konnov
  */
class SimplifyRecordAccess(tracker: TransformationTracker) extends TlaExTransformation {
  override def apply(ex: TlaEx) = transform(ex)

  def transform: TlaExTransformation = tracker.track {
    // main case
    case OperEx(TlaFunOper.app,
                OperEx(TlaFunOper.enum, ctorArgs @ _*),
                ValEx(TlaStr(accessedKey))) =>
      val rewrittenArgs = ctorArgs map transform
      val found = rewrittenArgs.grouped(2).find {
        case Seq(ValEx(TlaStr(key)), _) => key == accessedKey
      }
      found match {
        case Some(pair) => pair(1) // get the value
        case _ => throw new IllegalArgumentException(s"Access to non-existent record field $accessedKey")
      }

    // standard recursive processing for operators and let-in definitions
    case ex @ LetInEx(body, defs @ _*) =>
      // Transform bodies of all op.defs
      val newDefs = defs.map { x =>
        x.copy(body = transform(x.body))
      }
      val newBody = transform(body)
      if (defs == newDefs && body == newBody) {
        ex
      } else {
        LetInEx(newBody, newDefs: _*)
      }

    case ex@OperEx( op, args@_* ) =>
      val newArgs = args map transform
      if ( args == newArgs ) ex else OperEx( op, newArgs : _* )

    case ex => ex
  }
}

object SimplifyRecordAccess {
  def apply(tracker: TransformationTracker): SimplifyRecordAccess = {
    new SimplifyRecordAccess(tracker)
  }
}
