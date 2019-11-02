package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
  * <p>Attempts to instantiate the body of the operator named `name` with the provided arguments.
  * Returns None if the operator name is not a key in `bodyMap`, otherwise returns Some(b), where
  * b is the body of the operator with each formal parameter replaced by the corresponding value from `args`.</p>
  *
  * <p>Throws IllegalArgumentException if the size of `args` does not match the operator arity.</p>
  *
  * @author Jure Kukovec
  */
class Inline(defBodyMap: BodyMap, tracker: TransformationTracker)
    extends TlaExTransformation {

  override def apply(expr: TlaEx): TlaEx = {
    transform(expr)
  }

  def transform: TlaExTransformation = tracker.track {
    // interesting case: applying a user-defined operator
    case ex @ OperEx(TlaOper.apply, NameEx(name), args @ _*) =>
      // Jure, 5.7.19: Can 0-arity operators ever appear as standalone NameEx, without
      // a OperEx( TlaOper.apply, NameEx( name ), args@_* ) wrapper? Currently, we consider that invalid
      instantiateBody(name, args: _*).getOrElse(ex)

    // recursive processing of composite operators and let-in definitions
    case ex @ LetInEx(body, defs@_*) =>
      // transform bodies of all op.defs
      val newDefs = defs.map { x =>
        x.copy(body = transform(x.body))
      }
      val newBody = transform(body)
      if (defs == newDefs && body == newBody) {
        ex
      } else {
        LetInEx(newBody, newDefs: _*)
      }

    case ex@OperEx(op, args@_*) =>
      val newArgs = args map transform
      if (args == newArgs) ex else OperEx(op, newArgs: _*)

    case ex => ex
  }

  private def instantiateBody(name: String, args: TlaEx*): Option[TlaEx] = {
    defBodyMap.get(name) match {
      case Some((params, body)) if params.size == args.size =>
        // deep copy the body, to ensure uniqueness of the UIDs
        val bodyCopy = DeepCopy(tracker)(body)

        val newBody = params.zip(args).foldLeft(bodyCopy) {
          case (b, (fParam, arg)) =>
            ReplaceFixed(NameEx(fParam.name), arg, tracker)(b)
        }
        // newBody may contain calls to other operators, recurse
        val newInlinedBody = transform(newBody)
        Option(newInlinedBody)

      case Some((params, _)) if params.size != args.size =>
        val msg = s"Operator $name with arity ${params.size} called with ${args.size} argument(s)."
        throw new IllegalArgumentException(msg)

      case _ => None
    }
  }
}

object Inline {
  def apply(defBodyMap: BodyMap, tracker: TransformationTracker): Inline = {
    new Inline(defBodyMap, tracker)
  }
}
