package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations._
import at.forsyte.apalache.tla.lir._

/**
 * Replace every equality x' = e with x' \in {e}. This transformation is needed by the assignment solver,
 * so we extracted it into an optional transformation.
 *
 * @author Jure Kukovec
 */
@deprecated("To be removed in #564")
class PrimedEqualityToMembership(tracker: TransformationTracker)(implicit typeTag: TypeTag)
    extends TlaExTransformation {
  override def apply(ex: TlaEx): TlaEx = {
    transform(ex)
  }

  def transform: TlaExTransformation = tracker.trackEx {
    // interesting case
    case OperEx(TlaOper.eq, lhs @ OperEx(TlaActionOper.prime, NameEx(name)), rhs) =>
      OperEx(TlaSetOper.in, lhs, OperEx(TlaSetOper.enumSet, rhs))

    // standard recursive processing of composite operators and let-in definitions
    case ex @ LetInEx(body, defs @ _*) =>
      // Transform bodies of all op.defs
      val newDefs = defs map tracker.trackOperDecl { d => d.copy(body = transform(d.body)) }
      val newBody = transform(body)
      if (defs == newDefs && body == newBody) ex else LetInEx(newBody, newDefs: _*)

    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map transform
      if (args == newArgs) ex else OperEx(op, newArgs: _*)

    case ex => ex
  }
}

object PrimedEqualityToMembership {
  def apply(tracker: TransformationTracker)(implicit typeTag: TypeTag): PrimedEqualityToMembership = {
    new PrimedEqualityToMembership(tracker)
  }
}
