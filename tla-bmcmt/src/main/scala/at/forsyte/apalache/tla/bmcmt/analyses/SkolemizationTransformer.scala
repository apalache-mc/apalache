package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{BmcOper, TlaBoolOper, TlaControlOper}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.convenience._

/**
  * The skolemization analysis finds the existential quantifiers that can be safely replace by constants (skolemized).
  *
  * @author Igor Konnov
  */
class SkolemizationTransformer @Inject() (tracker: TransformationTracker)
    extends TlaExTransformation with LazyLogging {

  override def apply(e: TlaEx): TlaEx = { transform(e) }

  def transform: TlaExTransformation = tracker.track {
    case OperEx(TlaBoolOper.exists, name, set, pred) =>
      OperEx(BmcOper.skolemExists, tla.exists(name, set, transform(pred)))

    case OperEx(TlaBoolOper.forall, name, set, pred) =>
      // it is fine to skolemize existentials under \A, as \A is translated into a conjunction
      tla.forall(name, set, transform(pred))

    case ex @ OperEx(TlaBoolOper.not, _) =>
      ex // stop here. This should be a leaf (and rare) expression, as we are dealing with the NNF.

    case OperEx(TlaBoolOper.and, args@_*) =>
      tla.and(args map transform :_*)

    case OperEx(TlaBoolOper.or, args@_*) =>
      tla.or(args map transform :_*)

    case OperEx(TlaControlOper.ifThenElse, cond, left, right) =>
      // try to identify existentials in the both arms
      tla.ite(cond, transform(left), transform(right))
      // We omit skolemization of the existentials in the predicate,
      // as the predicate is used in both the negated and non-negated forms.
      // Effectively, IF-THEN-ELSE requires both \E and \A forms

    case LetInEx(body, defs @ _*) =>
      // at this point, we only have nullary let-in definitions
      def mapDef(df: TlaOperDecl) = {
        TlaOperDecl(df.name, df.formalParams, transform(df.body))
      }
      LetInEx(transform(body), defs map mapDef :_*)

    case OperEx(oper, args @ _*) =>
      // try to descend in the children, which may contain Boolean operations, e.g., { \E x \in S: P }
      OperEx(oper, args map transform :_*)

    case terminal =>
      terminal // terminal expression, stop here
  }

}
