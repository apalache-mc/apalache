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
class InlinerOfUserOper(defBodyMap: BodyMap, tracker: TransformationTracker)
    extends TlaExTransformation {

  override def apply(expr: TlaEx): TlaEx = {
    transform( stepLimitOpt = None )(expr)
  }

  def kStepInline( k : BigInt ) : TlaExTransformation =
    if (k <= 0) throw new IllegalArgumentException( "The number of allowed steps for kStepInline must be a positive integer." )
    else transform( stepLimitOpt = Some( k ) )

  def transform(stepLimitOpt: Option[BigInt]): TlaExTransformation = tracker.track {
    // interesting case: applying a user-defined operator
    case ex @ OperEx(TlaOper.apply, NameEx(name), args @ _*) =>
      // Jure, 5.7.19: Can 0-arity operators ever appear as standalone NameEx, without
      // a OperEx( TlaOper.apply, NameEx( name ), args@_* ) wrapper? Currently, we consider that invalid
      defBodyMap.get(name) match {
        case Some( decl ) if decl.formalParams.size == args.size =>
          instantiateWithArgs(stepLimitOpt)( decl, args )

        case Some(decl) if decl.formalParams.size != args.size =>
          val msg = s"Operator $name with arity ${decl.formalParams.size} called with ${args.size} argument(s)."
          throw new IllegalArgumentException(msg)

        case _ => ex
      }

    // recursive processing of composite operators and let-in definitions
    case ex @ LetInEx(body, defs@_*) =>
      // transform bodies of all op.defs
      val newDefs = defs.map { x =>
        x.copy(body = transform(stepLimitOpt)(x.body))
      }
      val newBody = transform(stepLimitOpt)(body)
      if (defs == newDefs && body == newBody) {
        ex
      } else {
        LetInEx(newBody, newDefs: _*)
      }

    case ex@OperEx(op, args@_*) =>
      val newArgs = args map transform(stepLimitOpt)
      if (args == newArgs) ex else OperEx(op, newArgs: _*)

    case ex => ex
  }

  private def instantiateWithArgs(stepLimitOpt: Option[BigInt])( decl: TlaOperDecl, args: Seq[TlaEx] ) : TlaEx = {
    // Assumption: |decl.formalParams| = |args|

    // deep copy the body, to ensure uniqueness of the UIDs
    val bodyCopy = DeepCopy( tracker )( decl.body )

    val newBody = decl.formalParams.zip( args ).foldLeft( bodyCopy ) {
      case (b, (fParam, arg)) =>
        ReplaceFixed( NameEx( fParam.name ), arg, tracker )( b )
    }

    // the step limit, if it was defined, decreases by 1
    val newStepLimit = stepLimitOpt map { _ - 1 }

    // if further steps are allowed then recurse otherwise terminate with current result
    if ( newStepLimit forall { _ > 0 } )
      transform(newStepLimit)( newBody )
    else
      newBody
  }
}

object InlinerOfUserOper {
  def apply(defBodyMap: BodyMap, tracker: TransformationTracker): InlinerOfUserOper = {
    new InlinerOfUserOper(defBodyMap, tracker)
  }
}
