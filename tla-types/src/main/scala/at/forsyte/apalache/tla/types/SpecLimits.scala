package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.TlaStr

class Enumeration( collection: Set[String] ) {
  private val forward : Array[String] = collection.toArray[String]
  private val backward: Map[String,  Int] = forward.zipWithIndex.toMap

  def getVal( i : Int ) : String = forward( i )
  def getIdx( v : String ) : Int = backward( v )
}

sealed case class SpecLimits(
                              maxIndex : Int,
                              fields : Set[String]
                            ) {
  def maxNumFields : Int = fields.size

  def getEnumeration = new Enumeration(fields)

}

object SpecLimits {

  private val defaultLimit = SpecLimits( 0, Set.empty[String] )

  private def unify( specLimits1 : SpecLimits, specLimits2 : SpecLimits ) : SpecLimits =
    SpecLimits(
      math.max( specLimits1.maxIndex, specLimits2.maxIndex ),
      specLimits1.fields.union( specLimits2.fields )
    )

  private def unifyCollection( col : Traversable[SpecLimits], init : SpecLimits = defaultLimit ) =
    col.foldLeft( init )( unify )


  private def getLimit( ex : TlaEx ) : SpecLimits = ex match {
    // Tuples may increase the index bound
    case OperEx( TlaFunOper.tuple, args@_* ) =>
      args.map( getLimit ).foldLeft( defaultLimit.copy( maxIndex = args.length ) )( unify )

    // Records may increase the field bounds
    case OperEx( TlaFunOper.enum, args@_* ) =>
      val fields = args.zipWithIndex collect {
        case (field, i) if i % 2 == 0 =>
          field match {
            case ValEx( TlaStr( s ) ) => s
            case _ => // sanity check
              throw new IllegalArgumentException( "Record constructor exception: Field name is not a string." )
          }
      }
      unifyCollection( args.map( getLimit ), defaultLimit.copy( fields = fields.toSet ) )

    // TODO: Investigate if enabling this matters
//    // Depending on the argument, function application may increase either the index or the field set
//    case OperEx( TlaFunOper.app, f, arg ) =>
//      val argLimit = arg match {
//        case ValEx( TlaInt( i ) ) => defaultLimit.copy( maxIndex = i.intValue() )
//        case ValEx( TlaStr( s ) ) => defaultLimit.copy( fields = Set( s ) )
//        case _ => getLimit( arg )
//      }
//      unify( argLimit, getLimit( f ) ) // it may happen that f is a complex expression

    // The number of arguments passed to an operator may update the max index
    // Unlike functions, operator names may not be complex, as no tla expression returns an operator
    case OperEx( TlaOper.apply, _, args@_* ) =>
      unifyCollection( args.map( getLimit ), defaultLimit.copy( maxIndex = args.length ) )

    case OperEx( _, args@_* ) =>
      unifyCollection( args.map( getLimit ), defaultLimit )

    case LetInEx( body, defs@_* ) =>
      defs.map( d => getLimit( d.body ) ).foldLeft( getLimit( body ) )( unify )

    case _ => defaultLimit
  }

  def getLimits( declarations : Traversable[TlaDecl] ) : SpecLimits = {

    val collection =
      declarations.withFilter(
        _.isInstanceOf[TlaOperDecl]
      ).map(
        d => getLimit( d.asInstanceOf[TlaOperDecl].body )
      )
    unifyCollection( collection )
  }

}
