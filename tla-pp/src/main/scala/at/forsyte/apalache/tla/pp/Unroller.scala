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

  def unrollLetIn(
                   bodyMap : BodyMap
                 ) : TlaExTransformation = tracker.track {
    case ex@LetInEx( body, defs@_* ) =>
      val newMap = BodyMapFactory.makeFromDecls( defs, bodyMap )
      val defaultsMap = getDefaults(newMap).getOrThrow
      val replaceTr = replaceWithDefaults( defaultsMap )
      val inliner = InlinerOfUserOper( newMap, tracker )
      val newDefs = defs map {
        replaceRecursiveDecl( _, newMap, inliner, replaceTr ).asInstanceOf[TlaOperDecl]
      }
      val newBody = unrollLetIn( newMap )( body )
      if ( defs == newDefs && body == newBody )
        ex
      else
        LetInEx( newBody, newDefs:_* )
    case ex@OperEx( op, args@_* ) =>
      val newArgs = args map unrollLetIn( bodyMap )
      if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
    case ex => ex
  }

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
    // We get the unrolling limit, which should be an operator in bodyMap.
    // note that operators inside named instances have a qualified name, e.g., I!Foo. Replace "!" with "_".
    val unrollLimitOperName = s"$UNROLL_TIMES_PREFIX$name".replace('!', '_')
    bodyMap.get( unrollLimitOperName ) match {
      case Some( unrollLimitDecl ) =>
        // The unrollLimit operator must not be recursive ...
        if ( unrollLimitDecl.isRecursive ) {
          val msg = s"Expected an integer bound in $unrollLimitOperName, found a recursive operator. See: " + MANUAL_LINK
          FailWith( new TlaInputError( msg ) )
        } else {
        // ... and must evaluate to a single integer
          ConstSimplifier( tracker )(
            InlinerOfUserOper( bodyMap, tracker )( unrollLimitDecl.body )
          ) match {
            case ValEx( TlaInt( n ) ) =>
              SucceedWith( n )
            case e =>
              FailWith( new TlaInputError(s"Expected an integer bound in $unrollLimitOperName, found: " + e) )
          }
        }

      case None =>
        val msg = s"Recursive operator $name requires an annotation $unrollLimitOperName. See: " + MANUAL_LINK
        FailWith( new TlaInputError( msg ) )
    }
  }

  def getDefaultBody( name : String, bodyMap : BodyMap ) : ExceptionOrValue[TlaEx] = {
    // note that operators inside named instances have a qualified name, e.g., I!Foo. Replace "!" with "_".
    val defaultOperName = s"$UNROLL_DEFAULT_PREFIX$name".replace('!', '_')
    bodyMap.get( defaultOperName ) match {
      case Some( defaultDecl ) =>
        // ... which must not be recursive ...
        if ( defaultDecl.isRecursive ) {
          val msg = s"Expected a default value in $defaultOperName, found a recursive operator. See: " + MANUAL_LINK
          FailWith( new TlaInputError( msg ) )
        } else {
          // ... but may be defined using other operators, so we call transform on it
          SucceedWith( InlinerOfUserOper( bodyMap, tracker )( defaultDecl.body ) )
        }

      case None =>
        FailWith( new TlaInputError( s"Recursive operator $name requires an annotation $defaultOperName. See: " + MANUAL_LINK ) )
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
      val unrolledLetIn = unrollLetIn( bodyMap )( body )
      val inlined = kStepInline( unrolledLetIn )
      val defaultReplaced = replaceWithDefaultsTr( inlined )
      TlaOperDecl( name, fparams, defaultReplaced )
    case d@TlaOperDecl( name, fparams, body ) => // d.isRecursive = false
      val unrolledLetIn = unrollLetIn( bodyMap )( body )
      if (body == unrolledLetIn)
        d
      else
        TlaOperDecl( name, fparams, unrolledLetIn )
    case TlaRecFunDecl( name, arg, dom, body ) =>
      // Ignore for now?
      decl
    case _ => decl
  }

  def getDefaults( bodyMap: BodyMap ) : ExceptionOrValue[ Map[String,TlaEx] ] = {
    val defMap = bodyMap.values withFilter {
      _.isRecursive
    } map {
      decl => decl.name -> getDefaultBody( decl.name, bodyMap )
    }
    val init : ExceptionOrValue[Map[String, TlaEx]] = SucceedWith( Map.empty[String, TlaEx] )
    defMap.foldLeft( init ) {
      case (SucceedWith( m ), (k, SucceedWith( v ))) =>
        SucceedWith( m + ( k -> v ) )
      case (fail : FailWith[Map[String, TlaEx]], _) => fail
      case (_, (_, fail : FailWith[TlaEx])) => FailWith[Map[String, TlaEx]]( fail.e )
    }
  }

  override def apply( module : TlaModule ) : TlaModule = {
    val operDecls = module.operDeclarations
    val bodyMap = BodyMapFactory.makeFromDecls( operDecls )
    val defaultsMap = getDefaults(bodyMap).getOrThrow
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
  val MANUAL_LINK: String = "https://github.com/informalsystems/apalache/blob/unstable/docs/manual.md#recursion"

  def apply( tracker : TransformationTracker ) : Unroller = {
    new Unroller( tracker )
  }
}