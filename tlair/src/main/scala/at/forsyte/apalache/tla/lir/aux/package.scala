package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaSetOper}

// Contains methods and classes used in testing/debugging/experimenting
package object aux {

  def aggregate[T](
                    join : (T, T) => T,
                    base : TlaEx => T
                  )
                  ( ex : TlaEx ) : T = {
    val self = aggregate[T]( join, base )( _ )
    ex match {
      case LetInEx( body, defs@_* ) =>
        join(
          self( body ),
          defs.map( _.body ).map( self ).foldLeft( base( ex ) ) {
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

    case LetInEx( body, defs@_* ) =>
      val opMaps = defs.map {
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

  /** We need to split an ordered collection of OperDecls (from a LET-IN operator),
    * into segments of 0 arity and >0 ariry operators, to expand all but the 0-arity
    */
  def collectSegments( decls : Traversable[TlaOperDecl] ) : List[List[TlaOperDecl]] = decls match {
    case d if d.isEmpty => List.empty
    case head :: tail =>
      val rec = collectSegments( tail )
      val headOrEmpty = rec.headOption.getOrElse( List.empty )
      // head has arity >0 && all decls in the first segment have arity >0.
      // if headOption returns None, the 2nd condition vacuously holds for the empty seq
      if ( head.formalParams.nonEmpty && headOrEmpty.forall( _.formalParams.nonEmpty ) )
        ( head +: headOrEmpty ) +: rec.drop( 1 ) // Nil.tail throws, but Nil.drop(1) doesn't
      else
        List( head ) +: rec
  }

}
