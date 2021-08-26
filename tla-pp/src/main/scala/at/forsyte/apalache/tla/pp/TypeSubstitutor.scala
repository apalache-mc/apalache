package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.typecheck.etc.Substitution

import javax.inject.Singleton

/**
 * <p>Apply a type substitution to the types of a subexpression.</p>
 *
 * @author Igor Konnov
 */
@Singleton
class TypeSubstitutor(tracker: TransformationTracker, sub: Substitution) extends TlaExTransformation {

  override def apply(expr: TlaEx): TlaEx = {
    transform(expr)
  }

  /**
   * Apply a substitution.
   *
   * @return a transformed set expression
   */
  def transform: TlaExTransformation = tracker.trackEx {
    case oper @ OperEx(op, args @ _*) =>
      val newArgs = args map transform
      val newOper =
        if (newArgs.map(_.ID) != args.map(_.ID)) {
          // Introduce a new operator only if the arguments have changed.
          // Otherwise, we would introduce lots of redundant chains in ChangeListener.
          tracker.hold(oper, OperEx(op, newArgs: _*)(oper.typeTag)) // fixes #41
        } else {
          oper
        }

      val reducedType = sub.subRec(oper.typeTag.asTlaType1())
      newOper.withTag(Typed(reducedType))

    case letInEx @ LetInEx(body, defs @ _*) =>
      def mapDecl(d: TlaOperDecl): TlaOperDecl = d.copy(body = transform(d.body))

      val reducedType = sub.subRec(letInEx.typeTag.asTlaType1())
      LetInEx(transform(body), defs.map(mapDecl): _*)(Typed(reducedType))

    case ex =>
      val reducedType = sub.subRec(ex.typeTag.asTlaType1())
      ex.withTag(Typed(reducedType))
  }
}
