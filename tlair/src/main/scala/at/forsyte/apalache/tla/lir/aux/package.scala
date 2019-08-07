package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.{LetInOper, TlaActionOper, TlaSetOper}

// Contains methods and classes used in testing/debugging/experimenting
package object aux {

  def aggregate[T](
                    join : (T, T) => T,
                    base : TlaEx => T
                  )
                  ( ex : TlaEx ) : T = {
    val self = aggregate[T]( join, base )( _ )
    ex match {
      case OperEx( letIn : LetInOper, body ) =>
        join(
          self( body ),
          letIn.defs.map( _.body ).map( self ).foldLeft( base( ex ) ) {
            join
          }
        )
      case OperEx( _, args@_* ) => args.map( self ).foldLeft( base( ex ) ) {
        join
      }
      case _ => base( ex )
    }
  }

  def allUidsBelow : TlaEx => Set[UID] = aggregate[Set[UID]](
    _ ++ _,
    ex => Set( ex.ID )
  )

  def uidToExMap : TlaEx => Map[UID, TlaEx] = aggregate[Map[UID, TlaEx]](
    _ ++ _,
    ex => Map( ex.ID -> ex )
  )

  def joinMaps( a : Map[String, Int], b : Map[String, Int] ) : Map[String, Int] = ( for {
    x <- a.keySet.union( b.keySet )
  } yield x -> ( a.getOrElse( x, 0 ) + b.getOrElse( x, 0 ) ) ).toMap[String, Int]

  def countCandidates( vars : Set[String], ex : TlaEx ) : Map[String, Int] = ex match {
    case OperEx( TlaSetOper.in, OperEx( TlaActionOper.prime, NameEx( s ) ), _ )
      if vars.contains( s ) => Map( s -> 1 )
    case OperEx( op : LetInOper, body ) =>
      val opMaps = op.defs.map {
        decl => countCandidates( vars, decl.body )
      }
      val bodyMap = countCandidates( vars, body )
      opMaps.foldLeft( bodyMap )( joinMaps )

    case OperEx( _, args@_* ) =>
      val argMaps = args map {
        countCandidates( vars, _ )
      }
      argMaps.foldLeft( Map.empty[String, Int] ) {
        joinMaps
      }
    case _ => Map.empty[String, Int]
  }

}
