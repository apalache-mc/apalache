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
    case operEx @ OperEx(op, args @ _*) =>
      val newArgs = args map transform
      val newOper =
        if (newArgs.map(_.ID) != args.map(_.ID)) {
          // Introduce a new operator only if the arguments have changed.
          // Otherwise, we would introduce lots of redundant chains in ChangeListener.
          tracker.hold(operEx, OperEx(op, newArgs: _*)(operEx.typeTag)) // fixes #41
        } else {
          operEx
        }

      val genericType = operEx.typeTag.asTlaType1()
      val reducedType = sub.subRec(genericType)
      if (reducedType != genericType) {
        newOper.withTag(Typed(reducedType))
      } else {
        newOper
      }

    case letInEx @ LetInEx(body, defs @ _*) =>
      def mapDecl(d: TlaOperDecl): TlaOperDecl = d.copy(body = transform(d.body))

      val genericType = letInEx.typeTag.asTlaType1()
      val reducedType = sub.subRec(genericType)
      LetInEx(transform(body), defs.map(mapDecl): _*)(Typed(reducedType))

    case ex =>
      val genericType = ex.typeTag.asTlaType1()
      val reducedType = sub.subRec(genericType)
      if (reducedType != genericType) {
        ex.withTag(Typed(reducedType))
      } else {
        ex
      }
  }
}
