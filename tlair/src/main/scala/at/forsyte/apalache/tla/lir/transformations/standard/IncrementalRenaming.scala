package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

import scala.collection.immutable.HashMap

object IncrementalRenaming {
  private val separator : String = "$"
  private val separatorRegex = s"[$separator]"

  def makeName( base: String, ctr: Int ) : String = s"$base$separator$ctr"

  type counterMapType = Map[String,Int]

  def parseName( name : String ) : Option[(String, Int)] = {
    name.split( separatorRegex ) match {
      // Already renamed before
      case Array( n, i ) if i forall {_.isDigit} => Some((n, i.toInt))
      // Never renamed before
      case Array( n ) => None
      // Error
      case _ => throw new IllegalArgumentException("Variable names should never contain more than one separator")
    }
  }

  def getBase( name : String ) : String = parseName( name ).map( _._1 ).getOrElse( name )

  def mergeNameCounters( takeMax: Boolean )( m1 : counterMapType, m2 : counterMapType ) : counterMapType = {
    val selectorFun : (Int, Int) => Int = if (takeMax) math.max else math.min
    m2.foldLeft( m1 ) { case (m, (k, v)) =>
      m + ( k -> selectorFun( m1.getOrElse( k, v ), v ) )
    }
  }


  def nameCounterMapFromDecls( decls: Traversable[TlaDecl] ) : counterMapType =
    decls.map( nameCounterMapFromDecl ).foldLeft( Map.empty[String, Int] ) { mergeNameCounters( takeMax = true ) }

  def nameCounterMapFromDecl( decl : TlaDecl ) : counterMapType = decl match {
    case TlaOperDecl( name, params, body ) =>
      val nameAndParamMap = ( parseName( name ) ++: params.flatMap( p => parseName( p.name ) ) ).toMap
      val bodyMap = nameCounterMapFromEx( body )
      mergeNameCounters( takeMax = true )( bodyMap, nameAndParamMap )
    case _ => Map.empty
  }

  def nameCounterMapFromEx( ex: TlaEx ) : counterMapType = ex match {
    case NameEx( n ) => parseName( n ) match {
      case Some((base, ctr)) => Map( base -> ctr )
      case None => Map.empty // No need to store n -> 0
    }

    case OperEx( _, args@_* ) =>
      args.map( nameCounterMapFromEx ).foldLeft(Map.empty[String,Int]){ mergeNameCounters( takeMax = true ) }

    case LetInEx( body, defs@_* ) =>
      defs.map( nameCounterMapFromDecl ).foldLeft( nameCounterMapFromEx( body ) ) {
        mergeNameCounters( takeMax = true )
      }

    case _ => Map.empty
  }
}

/**
  * Unlike Renaming, IncrementalRenaming is intended to maintain concise names under arbitrary re-application
  */
class IncrementalRenaming( tracker : TransformationTracker ) extends TlaExTransformation {

  import IncrementalRenaming._

  private var nameCounters : Map[String, Int] = HashMap.empty[String, Int]

  private def getNextUnique( base : String ) : String = {
    val newCtr = 1 + nameCounters.getOrElse( base, 0 )
    nameCounters += base -> newCtr

    makeName( base, newCtr )
  }

  private def getNextUniqueFromBase( name: String ) = getNextUnique( getBase( name ) )

  private def trackedSubstitution( x : TlaEx, y : TlaEx ) = tracker.track( _ => y )( x )

  def rename( alreadyRenamed: Map[String,String] ): TlaExTransformation = tracker.track {
    case ex @ NameEx(name) =>
      if ( alreadyRenamed.contains( name ) ) trackedSubstitution( ex, NameEx( alreadyRenamed( name ) ) )
      else ex

    case OperEx(op, nex@NameEx(name), otherArgs@_*)
      if op == TlaSetOper.filter
        || op == TlaBoolOper.exists || op == TlaBoolOper.forall
        || op == TlaOper.chooseBounded || op == TlaOper.chooseUnbounded
        || op == TlaOper.chooseIdiom =>
      val newName = getNextUniqueFromBase( name )
      val newRenamed = alreadyRenamed + (name -> newName)
      val newArgs = otherArgs.map( rename( newRenamed ) )
      OperEx( op, trackedSubstitution( nex, NameEx( newName ) ) +: newArgs : _* )

    case OperEx(op, result, varsAndSets@_*)
      if op == TlaSetOper.map || op == TlaFunOper.funDef =>
      val names = varsAndSets.zipWithIndex.collect { case (e @ NameEx(_), i) if i % 2 == 0 => e }

      val newRenamed = names.map(_.name).foldLeft(alreadyRenamed) { case (m, n) =>
        m + ( n -> getNextUniqueFromBase( n ) )
      }

      val newArgs = (result +: varsAndSets).map { rename(newRenamed) }

      OperEx(op, newArgs: _*)

    case ex@OperEx(op, args@_*) =>
      val newArgs = args.map( rename( alreadyRenamed ) )
      if ( args == newArgs ) ex
      else OperEx( op, newArgs : _* )

    case LetInEx( body, defs@_* ) =>
      val opersAndFParamsNameMap = ( defs flatMap {
        case TlaOperDecl( n, params, _ ) => ( n -> getNextUniqueFromBase( n ) ) +: (
          params map { p =>
            val pName = p.name
            pName -> getNextUniqueFromBase( pName )
          } )
      } ).toMap

      val newRenamed = alreadyRenamed ++ opersAndFParamsNameMap

      val newRenaming = rename( newRenamed )

      val newDefs = defs map {
        case TlaOperDecl( n, ps, b ) =>
          TlaOperDecl(
            opersAndFParamsNameMap( n ),
            ps map {
              case SimpleFormalParam( p ) => SimpleFormalParam( opersAndFParamsNameMap( p ) )
              case OperFormalParam( p, a ) => OperFormalParam( opersAndFParamsNameMap( p ), a )
            },
            newRenaming( b )
          )
      }
      val newBody = newRenaming( body )
      LetInEx( newBody, newDefs : _* )

    case ex => ex
  }

  override def apply( ex : TlaEx ) : TlaEx = rename( alreadyRenamed = Map.empty )( ex )

}
