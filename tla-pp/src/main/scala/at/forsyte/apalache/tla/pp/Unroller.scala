package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.aux.{ExceptionOrValue, FailWith, SucceedWith}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.storage.{BodyMap, BodyMapFactory}
import at.forsyte.apalache.tla.lir.transformations.standard.InlinerOfUserOper
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TlaModuleTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.TlaInt

class Unroller( tracker : TransformationTracker ) extends TlaModuleTransformation {

  import Unroller._

  def replaceWithDefaults( defaultsMap : Map[String, TlaEx] ) : TlaExTransformation = tracker.track {
    case ex@OperEx( TlaOper.apply, NameEx( name ), args@_* ) =>
      defaultsMap.getOrElse( name, ex )
    // recursive processing of composite operators and let-in definitions
    case ex@LetInEx( body, defs@_* ) =>
      // transform bodies of all op.defs
      val transform = replaceWithDefaults( defaultsMap )
      val newDefs = defs.map { x =>
        x.copy( body = transform( x.body ) )
      }
      val newBody = transform( body )
      if ( defs == newDefs && body == newBody ) {
        ex
      } else {
        LetInEx( newBody, newDefs : _* )
      }

    case ex@OperEx( op, args@_* ) =>
      val newArgs = args map replaceWithDefaults( defaultsMap )
      if ( args == newArgs ) ex else OperEx( op, newArgs : _* )

    case ex => ex
  }


  def getUnrollLimit( name : String, bodyMap : BodyMap ) : ExceptionOrValue[BigInt] = {
    // We get the unrolling limit, which should be an operator in bodyMap:
    val unrollLimitOperName = s"$UNROLL_TIMES_PREFIX$name"
    bodyMap.get( unrollLimitOperName ) match {
      case Some( unrollLimitDecl ) =>
        // The unrollLimit operator must not be recursive ...
        if ( unrollLimitDecl.isRecursive )
          FailWith( new Exception( s"Unroll-limit operator $unrollLimitOperName is recursive." ) )
        else
        // ... and must evaluate to a single integer
          InlinerOfUserOper( bodyMap, tracker )( unrollLimitDecl.body ) match {
            case ValEx( TlaInt( n ) ) =>
              SucceedWith( n )
            case _ =>
              FailWith( new Exception( s"Unroll-limit operator $unrollLimitOperName body must be a single integer." ) )
          }
      case None =>
        FailWith( new Exception( s"Unroll-limit operator $unrollLimitOperName for $name is not defined." ) )
    }
  }

  def getDefaultBody( name : String, bodyMap : BodyMap ) : ExceptionOrValue[TlaEx] = {
    val defaultOperName = s"$UNROLL_DEFAULT_PREFIX$name"
    bodyMap.get( defaultOperName ) match {
      case Some( defaultDecl ) =>
        // ... which must not be recursive ...
        if ( defaultDecl.isRecursive )
          FailWith( new Exception( s"Default body operator $defaultOperName is recursive." ) )
        else
        // ... but may be defined using other operators, so we call transform on it
          SucceedWith( InlinerOfUserOper( bodyMap, tracker )( defaultDecl.body ) )
      case None =>
        FailWith( new Exception( s"Default body operator $defaultOperName for $name is not defined." ) )
    }
  }

  def replaceRecursiveDecl(
                            decl : TlaDecl,
                            bodyMap : BodyMap,
                            inliner : InlinerOfUserOper,
                            replaceWithDefaultsTr : TlaExTransformation
                          ) : TlaDecl = decl match {
    case d@TlaOperDecl( name, fparams, body ) if d.isRecursive =>
      val unrollLimit = getUnrollLimit( name, bodyMap ).getOrThrow
      val kStepInline = inliner.kStepInline( unrollLimit )
      val inlined = kStepInline( body )
      val defaultReplaced = replaceWithDefaultsTr( inlined )
      TlaOperDecl( name, fparams, defaultReplaced )
    case TlaRecFunDecl( name, arg, dom, body ) =>
      // Ignore for now?
      decl
    case _ => decl
  }

  override def apply( module : TlaModule ) : TlaModule = {
    val operDecls = module.operDeclarations
    val bodyMap = BodyMapFactory.makeFromDecls( operDecls )
    val defaultsMap = ( operDecls withFilter {
      _.isRecursive
    } map { decl =>
      decl.name -> getDefaultBody( decl.name, bodyMap ).getOrThrow
    } ).toMap
    val replaceTr = replaceWithDefaults( defaultsMap )
    val inliner = InlinerOfUserOper( bodyMap, tracker )
    val newDecls = module.declarations map {
      replaceRecursiveDecl( _, bodyMap, inliner, replaceTr )
    }

    new TlaModule( module.name, newDecls )
  }
}

object Unroller {
  val UNROLL_TIMES_PREFIX   : String = "UNROLL_TIMES_"
  val UNROLL_DEFAULT_PREFIX : String = "UNROLL_DEFAULT_"

  def apply( tracker : TransformationTracker ) : Unroller = {
    new Unroller( tracker )
  }
}