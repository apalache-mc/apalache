package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper.{BmcOper, TlaOper}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TlaModuleTransformation, TransformationTracker}

/** Replaces instances of user-defined operator applications with a LET-IN wrapper.
  *
  * Example:
  * A(x,y) ~~> LET App_1 == A(x,y) IN App_1
  *
  * Operator constants and formal parameters are ignored.
  */
class AppWrap(
               nameGenerator : UniqueNameGenerator,
               tracker : TransformationTracker
             ) {

  import AppWrap.NAME_PREFIX

  private def setTracking( oldEx : => TlaEx, newEx : => TlaEx ) : TlaEx = {
    val tr = tracker.track {
      _ => newEx
    }
    tr( oldEx )
  }

  def wrap( wrappableNames : Set[String] ) : TlaExTransformation = tracker.track {
    case ex@OperEx( TlaOper.apply, NameEx( opName ), args@_* ) if wrappableNames.contains( opName ) && args.nonEmpty =>
      val newArgs = args map wrap( wrappableNames )
      val newEx =
        if ( args == newArgs ) ex
        else setTracking( ex, Builder.appOp( NameEx( opName ), newArgs : _* ) )

      val newName = s"${NAME_PREFIX}_${opName}_${nameGenerator.newName()}"
      val newDecl = TlaOperDecl( newName, List.empty, newEx )
      LetInEx( Builder.appDecl( newDecl ), newDecl )
      // On type annot. ignore the RHS
    case ex@OperEx( BmcOper.withType, argEx, typeEx ) =>
      val newArg = wrap( wrappableNames )(argEx)
      if ( argEx == newArg )
        ex
      else
        OperEx( BmcOper.withType, newArg, typeEx )
    case ex@OperEx( oper, args@_* ) =>
      val newArgs = args map wrap( wrappableNames )
      if ( args == newArgs )
        ex
      else
        OperEx( oper, newArgs : _* )
    case ex@LetInEx( body, defs@_* ) =>
      // Assumption: let-in defined operators are defined in dependency order
      val (newWrappable, newDefs) = defs.foldLeft( (wrappableNames, Seq.empty[TlaOperDecl]) ) {
        case ((partialSet, partialDecls), decl) =>
          val newDecl = decl.copy( body = wrap( partialSet )( decl.body ) )
          newDecl.isRecursive = decl.isRecursive
          (partialSet + decl.name, partialDecls :+ newDecl)
      }
      val newBody = wrap( newWrappable )( body )
      if ( body == newBody && defs == newDefs )
        ex
      else
        LetInEx( newBody, newDefs : _* )
    case ex => ex
  }

  def moduleTransform( wrappableNames : Set[String] ): TlaModuleTransformation = { m =>

    val newDecls = m.declarations map {
      case TlaOperDecl( name, params, body ) =>
        TlaOperDecl( name, params, wrap( wrappableNames )(body) )
      case d => d
    }
    new TlaModule( m.name, newDecls )
  }
}

object AppWrap {
  val NAME_PREFIX = "APP"

  def apply(
             nameGenerator : UniqueNameGenerator,
             tracker : TransformationTracker
           ) = new AppWrap( nameGenerator, tracker )
}
