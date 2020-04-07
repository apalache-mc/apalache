package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.TlaInt

import scala.collection.mutable

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

  import InlinerOfUserOper.{UNFOLD_DEFAULT_PREFIX, UNFOLD_TIMES_PREFIX}

  private var unfoldCount : mutable.Map[String, Int] = mutable.Map.empty
  // We will only compute limits if we need them.
  private var unfoldLimits : mutable.Map[String,BigInt] = mutable.Map.empty

  override def apply(expr: TlaEx): TlaEx = {
    unfoldCount = mutable.Map.empty
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

  private def normalCase( decl: TlaOperDecl, args: Seq[TlaEx] ) : Option[TlaEx] = {
    // Assumption: |decl.formalParams| = |args|

    // deep copy the body, to ensure uniqueness of the UIDs
    val bodyCopy = DeepCopy( tracker )( decl.body )

    val newBody = decl.formalParams.zip( args ).foldLeft( bodyCopy ) {
      case (b, (fParam, arg)) =>
        ReplaceFixed( NameEx( fParam.name ), arg, tracker )( b )
    }
    // newBody may contain calls to other operators, recurse
    val newInlinedBody = transform( newBody )
    Option( newInlinedBody )
  }

  private def instantiateBody(name: String, args: TlaEx*): Option[TlaEx] = {
    defBodyMap.get(name) match {
      case Some( decl ) if decl.formalParams.size == args.size =>
        // Check if recursive
        if ( decl.isRecursive ) {
          // We increment the recursion counter for this name
          val unfoldedTimes = unfoldCount.getOrElse( name, 0 ) + 1
          unfoldCount.put( name, unfoldedTimes )

          // We get the unfolding limit, which should be an operator in defBodyMap:
          val unfoldLimitOperName = s"$UNFOLD_TIMES_PREFIX$name"

          val unfoldLimit = unfoldLimits.getOrElseUpdate( unfoldLimitOperName,
            // If it is not yet known, we have to look up the defining operator
            defBodyMap.get( unfoldLimitOperName ) match {
              case Some( unfoldLimitDecl ) =>
                // The unfoldLimit operator must not be recursive ...
                if ( unfoldLimitDecl.isRecursive )
                  throw new Exception( s"Unfold-limit operator $unfoldLimitOperName is recursive." )
                else
                  // ... and must evaluate to a single integer
                  transform(unfoldLimitDecl.body) match {
                    case ValEx( TlaInt( n ) ) => n
                    case _ => throw new Exception( s"Unfold-limit operator $unfoldLimitOperName body must be a single integer." )
                  }
              case None => throw new Exception( s"Unfold-limit operator $unfoldLimitOperName for $name is not defined." )
            }
          )
          // Check if unfold limit is exceeded:
          if ( unfoldedTimes > unfoldLimit ) {
            // If yes, reset the unfold counter and call the default body operator ...
            unfoldCount.remove( name )
            val defaultOperName = s"$UNFOLD_DEFAULT_PREFIX$name"
            defBodyMap.get( defaultOperName ) match {
              case Some( defaultDecl ) =>
                // ... which must not be recursive ...
                if ( defaultDecl.isRecursive )
                  throw new Exception( s"Default body operator $unfoldLimitOperName is recursive." )
                else
                  // ... but may be defined using other operators, so we call transform on it
                  Some( transform(defaultDecl.body) )
              case None => throw new Exception( s"Default body operator $defaultOperName for $name is not defined." )
            }
          }
          else normalCase( decl, args )
        }
        else normalCase( decl, args )

      case Some(decl) if decl.formalParams.size != args.size =>
        val msg = s"Operator $name with arity ${decl.formalParams.size} called with ${args.size} argument(s)."
        throw new IllegalArgumentException(msg)

      case _ => None
    }
  }
}

object InlinerOfUserOper {

  // Jure, 2.4.20: By Igor's request, MC recursion specification operators have naming conventions
  val UNFOLD_TIMES_PREFIX : String = "UNFOLD_TIMES_"
  val UNFOLD_DEFAULT_PREFIX : String = "UNFOLD_DEFAULT_"

  def apply(defBodyMap: BodyMap, tracker: TransformationTracker): InlinerOfUserOper = {
    new InlinerOfUserOper(defBodyMap, tracker)
  }
}
