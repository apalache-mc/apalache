package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaControlOper}
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
  * The skolemization analysis finds the existential quantifiers that are safe to skolemize.
  *
  * @author Igor Konnov
  */
class SimpleSkolemization @Inject()
        (val frexStore: FreeExistentialsStoreImpl, tracker: TransformationTracker) extends LazyLogging {
  def markFreeExistentials(ex: TlaEx): Unit = ex match {
    case OperEx(TlaBoolOper.exists, name, _, pred) =>
      logger.debug(s"added free existential $name (id=${ex.ID})")
      frexStore.store += ex.ID
      markFreeExistentials(pred)

    case OperEx(TlaBoolOper.forall, _, _, pred) =>
      // it is fine to skolemize existentials under \A, as \A is translated into a conjunction
      markFreeExistentials(pred)

    case OperEx(TlaBoolOper.not, _) =>
      () // stop here. This should be a leaf (and rare) expression, as we are dealing with the NNF.

    case OperEx(TlaBoolOper.and, args@_*) =>
      args foreach markFreeExistentials

    case OperEx(TlaBoolOper.or, args@_*) =>
      args foreach markFreeExistentials

    case OperEx(TlaControlOper.ifThenElse, _, left, right) =>
      // try to identify existentials in the both arms
      markFreeExistentials(left)
      markFreeExistentials(right)
      // We omit skolemization of the existentials in the predicate,
      // as the predicate is used in both the negated and non-negated forms.
      // Effectively, IF-THEN-ELSE requires both \E and \A forms

    case LetInEx(body, defs @ _*) =>
      // at this point, we only have nullary let-in definitions
      defs.foreach { df => markFreeExistentials(df.body) }
      markFreeExistentials(body)

    case OperEx(_, args @ _*) =>
      // try to descend in the children, which may contain Boolean operations, e.g., { \E x \in S: P }
      args foreach markFreeExistentials

    case _ =>
      () // terminal expression, stop here
  }

}
