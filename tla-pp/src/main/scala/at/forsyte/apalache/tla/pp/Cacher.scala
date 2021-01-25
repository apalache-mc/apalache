package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TlaModuleTransformation, TransformationTracker}

class Cacher( nameGenerator: UniqueNameGenerator, tracker : TransformationTracker ) extends TlaModuleTransformation {

  def prepareAppMap( operNames: Set[String], init : Map[TlaEx, String] = Map.empty ) : TlaEx => Map[TlaEx, String] = {
    def inner(
               initialMap : Map[TlaEx, String],
               ex : TlaEx
             ) : Map[TlaEx, String]
    = ex match {
      case OperEx( TlaOper.apply, NameEx( operName ), args@_* ) if operNames.contains(operName) =>
        val newMap = // args will be syntactically matched
          if ( initialMap.contains( ex ) ) initialMap
          else initialMap + ( ex -> nameGenerator.newName() )
        args.foldLeft( newMap ) {
          inner
        }
      case OperEx( _, args@_* ) =>
        args.foldLeft( initialMap ) {
          inner
        }
      case LetInEx( body, defs@_* ) =>
        defs.map( _.body ).foldLeft( inner( initialMap, body ) ) {
          inner
        }
      case _ => initialMap
    }

    inner(init,_)
  }

  def replaceApplicationsWithNullary(
                                      operNames: Set[String],
                                      appMap: Map[TlaEx, String],
                                      letInDecisionFn: TlaOperDecl => Boolean
                                    ) : TlaExTransformation = tracker.trackEx {
    case ex@OperEx( TlaOper.apply, opName@NameEx( operName ), args@_* ) if operNames.contains(operName) =>
      // Assume ex is in the domain of appMap
      appMap.get( ex ).map(
        n => OperEx( TlaOper.apply, NameEx( n ) )
      ).getOrElse {
        val newArgs = args map replaceApplicationsWithNullary(operNames, appMap, letInDecisionFn)
        if ( args == newArgs ) ex else OperEx( TlaOper.apply, opName +: newArgs : _* )
      }

    case ex@OperEx( op, args@_* ) =>
      val newArgs = args map replaceApplicationsWithNullary(operNames, appMap, letInDecisionFn)
      if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
    case ex@LetInEx( body, defs@_* ) =>
      // LET-IN introduces new operators which may or may not be added
      val extendedOperNames = operNames ++ defs.withFilter( letInDecisionFn ).map( _.name )
      val modifiedDefs = defs map { cacheApplicaitons(extendedOperNames, letInDecisionFn)(_).asInstanceOf[TlaOperDecl] }
      val extendedAppMap = prepareAppMap( extendedOperNames, appMap )( body )
      val diffMap = extendedAppMap -- appMap.keySet
      val extendedDefs = diffMap.toSeq map {
        case (k, v) => TlaOperDecl( v, List.empty,
          fixPointRepeat( replaceApplicationsWithNullary( extendedOperNames, diffMap - k, letInDecisionFn ), k )
        )
      }
      val newDefs = modifiedDefs ++ extendedDefs
      val newBody = replaceApplicationsWithNullary(extendedOperNames, extendedAppMap, letInDecisionFn )( body )
      if ( defs == newDefs && body == newBody ) ex
      else LetInEx( newBody, newDefs : _* )
    case ex => ex
  }

  def fixPointRepeat[T]( fn : T => T, arg : T, limit : Int = 10 ) : T = {
    if ( limit <= 0 ) arg
    else {
      val newArg = fn( arg )
      if ( newArg == arg ) newArg
      else fixPointRepeat( fn, newArg, limit - 1 )
    }
  }


  def cacheApplicaitons(
                         operNames: Set[String],
                         letInDecisionFn: TlaOperDecl => Boolean
                       ) : TlaDecl => TlaDecl = {
    case decl@TlaOperDecl( _, _, body ) =>
      val appMap = prepareAppMap( operNames )( body )
      val letInBodyCandidate =
        replaceApplicationsWithNullary( operNames, appMap, letInDecisionFn )( body )
      if (body == letInBodyCandidate)
        decl
      else {

        val newBody =
          if ( appMap.isEmpty ) {
            letInBodyCandidate
          } else {
            val defs = appMap.toSeq map {
              case (k, v) => TlaOperDecl( v, List.empty,
                fixPointRepeat( replaceApplicationsWithNullary( operNames, appMap - k, letInDecisionFn ), k )
              )
            }
            LetInEx( letInBodyCandidate, defs : _* )
          }
        val newDecl = decl.copy( body = newBody )
        // copy does not preserve _.isRecursive
        newDecl.isRecursive = decl.isRecursive
        newDecl
      }
    case decl => decl
  }

  override def apply( module : TlaModule ) : TlaModule = {

    val operDecls = module.operDeclarations

    val recursive = operDecls.withFilter( _.isRecursive ).map( _.name ).toSet
    val newDecls = module.declarations map {
      cacheApplicaitons( recursive, Cacher.DecisionFns.recursive )
    }

    new TlaModule( module.name, newDecls )

  }
}


object Cacher {

  object DecisionFns {
    val recursive : TlaOperDecl => Boolean = _.isRecursive
    val all : TlaOperDecl => Boolean = { _ => true}
  }

  def apply( nameGenerator: UniqueNameGenerator, tracker : TransformationTracker ) : Cacher = {
    new Cacher( nameGenerator, tracker )
  }
}