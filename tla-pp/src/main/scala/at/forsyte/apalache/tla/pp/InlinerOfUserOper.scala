package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.lir.transformations.standard.{DeepCopy, ReplaceFixed}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.pp.InlinerOfUserOper.kStepParameters

/**
 * <p>Attempts to instantiate the body of the operator named `name` with the provided arguments.
 * Returns None if the operator name is not a key in `bodyMap`, otherwise returns Some(b), where
 * b is the body of the operator with each formal parameter replaced by the corresponding value from `args`.</p>
 *
 * <p>Throws IllegalArgumentException if the size of `args` does not match the operator arity.</p>
 *
 * @author Jure Kukovec
 */
class InlinerOfUserOper(defBodyMap: BodyMap, tracker: TransformationTracker) extends TlaExTransformation {

  override def apply(expr: TlaEx): TlaEx = {
    transform(stepLimitOpt = None)(expr)
  }

  def kStepInline(k: BigInt, post: TlaExTransformation = Predef.identity): TlaExTransformation =
    if (k < 0) throw new IllegalArgumentException("The number of unrolling steps must be a non-negative integer.")
    // 0-step is always just the identity transform, even if post is non-trivial, because, conceptually,
    // 0-step inlining is a no-op
    else if (k == 0) Predef.identity
    else transform(stepLimitOpt = Some(kStepParameters(k, post)))

  def transform(stepLimitOpt: Option[kStepParameters]): TlaExTransformation = tracker.trackEx {
    // interesting case: applying a user-defined operator
    case ex @ OperEx(TlaOper.apply, NameEx(name), args @ _*) =>
      // Jure, 5.7.19: Can 0-arity operators ever appear as standalone NameEx, without
      // a OperEx( TlaOper.apply, NameEx( name ), args@_* ) wrapper? Currently, we consider that invalid
      defBodyMap.get(name) match {
        case Some(decl) if decl.formalParams.size == args.size =>
          instantiateWithArgs(stepLimitOpt)(decl, args).withTag(ex.typeTag)

        case Some(decl) if decl.formalParams.size != args.size =>
          val msg = s"Operator $name with arity ${decl.formalParams.size} called with ${args.size} argument(s)."
          throw new IllegalArgumentException(msg)

        case _ => ex
      }

    // recursive processing of composite operators and let-in definitions
    case ex @ LetInEx(body, defs @ _*) =>
      // transform bodies of all op.defs
      val newDefs = defs map tracker.trackOperDecl { d => d.copy(body = transform(stepLimitOpt)(d.body)) }
      val newBody = transform(stepLimitOpt)(body)
      if (defs == newDefs && body == newBody) {
        ex
      } else {
        LetInEx(newBody, newDefs: _*)(ex.typeTag)
      }

    case ex @ OperEx(op, args @ _*) =>
      val newArgs = args map transform(stepLimitOpt)
      if (args == newArgs) ex else OperEx(op, newArgs: _*)(ex.typeTag)

    case ex => ex
  }

  private def instantiateWithArgs(stepLimitOpt: Option[kStepParameters])(decl: TlaOperDecl, args: Seq[TlaEx]): TlaEx = {
    // Assumption: |decl.formalParams| = |args|

    val postTr = stepLimitOpt map {
      _.postTransform
    } getOrElse {
      Predef.identity[TlaEx] _
    }
    // deep copy the body, to ensure uniqueness of the UIDs
    val bodyCopy = postTr(DeepCopy(tracker).deepCopyEx(decl.body))

    val newBody = decl.formalParams.zip(args).foldLeft(bodyCopy) { case (b, (fParam, arg)) =>
      ReplaceFixed(tracker)(NameEx(fParam.name)(arg.typeTag), arg)(b)
    }

    // If the operator has a parametric signature, we have to substitute type parameters with concrete parameters
    // 1. Unify the operator type with the arguments.
    // 2. Apply the resulting substitution to the types in all subexpressions.
    val actualSignature = OperT1(args.map(_.typeTag.asTlaType1()), bodyCopy.typeTag.asTlaType1())

    // the step limit, if it was defined, decreases by 1
    val newStepLimit = stepLimitOpt map {
      _ - 1
    }

    // if further steps are allowed then recurse otherwise terminate with current result
    if (
        newStepLimit forall {
          _ > 0
        }
    ) {
      transform(newStepLimit)(newBody)
    } else
      newBody
  }
}

object InlinerOfUserOper {

  sealed case class kStepParameters(k: BigInt, postTransform: TlaExTransformation) {
    def -(x: BigInt): kStepParameters = kStepParameters(k - x, postTransform)

    def >(x: BigInt): Boolean = k > x
  }

  def apply(defBodyMap: BodyMap, tracker: TransformationTracker): InlinerOfUserOper = {
    new InlinerOfUserOper(defBodyMap, tracker)
  }
}
