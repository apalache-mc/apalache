package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper._

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

  def hasPositiveArity( decl: TlaOperDecl ) : Boolean = decl.formalParams.nonEmpty

  /** We may need to split an ordered collection of OperDecls (from a LET-IN operator),
    * into segments of 0 arity and >0 ariry operators
    */
  def collectSegments( decls : Traversable[TlaOperDecl] ) : List[List[TlaOperDecl]] = decls match {
    case d if d.isEmpty => List.empty
    case head :: tail =>
      val headPosArity = hasPositiveArity( head )
      val rec = collectSegments( tail )
      val recHeadOrEmpty = rec.headOption.getOrElse( List.empty )
      // We merge to previous, if they have the same arity category (0 or >0)
      // if headOption returns None, the condition vacuously holds for the empty seq
      if ( recHeadOrEmpty.forall( d => hasPositiveArity( d ) == headPosArity ) )
        ( head +: recHeadOrEmpty ) +: rec.drop( 1 ) // Nil.tail throws, but Nil.drop(1) doesn't
      else
        List( head ) +: rec
  }

  def diff( ex1 : TlaEx, ex2: TlaEx ) : TlaEx = (ex1, ex2) match {
    case (OperEx( op1, args1@_* ), OperEx(op2, args2@_*)) if op1 == op2 =>
        val argDiff = args1.zipAll( args2, NullEx, NullEx ) map { case (x, y) => diff( x, y ) }
        OperEx( op1, argDiff: _* )
    case (ValEx(v1), ValEx(v2)) if v1 == v2 => ex1
    case (NameEx(n1), NameEx(n2)) if n1 == n2 => ex1
    case (LetInEx(b1, decls1@_*), LetInEx(b2, decls2@_*) ) =>
      val defaultDecl = TlaOperDecl("Null", List.empty, NullEx)
      val defaultParam = SimpleFormalParam("diffParam")
      val declDiff = decls1.zipAll( decls2, defaultDecl, defaultDecl ) map { case (d1, d2) =>
        if ( d1.name == d2.name && d1.formalParams == d2.formalParams )
          d1.copy( body = diff( d1.body, d2.body ) )
        else {
          val name = s"DiffDecl_${d1.name}_${d2.name}"
          val params = d1.formalParams.zipAll( d2.formalParams, defaultParam, defaultParam ) map {
            case (par1@SimpleFormalParam( p1 ), SimpleFormalParam( p2 )) if p1 == p2 =>
              par1
            case (par1@OperFormalParam( p1, FixedArity( n1 ) ), OperFormalParam( p2, FixedArity( n2 ) )) if p1 == p2 && n1 == n2 =>
              par1
            case (par1, par2) =>
              SimpleFormalParam( s"DiffParam_${par1.name}_${par2.name}" )
          }
          TlaOperDecl( name, params, diff( d1.body, d2.body ) )
        }
      }
      LetInEx( diff( b1, b2 ), declDiff : _* )
    case _ =>
      OperEx( TlaOper.apply, NameEx("Diff"), ex1, ex2 )
  }

  def allDiffs( ex : TlaEx ) : Seq[TlaEx] = ex match {
      case OperEx( TlaOper.apply, NameEx( "Diff" ), ex1, ex2 ) =>
        Seq(ex)
      case OperEx( _, args@_* ) =>
        args flatMap { allDiffs }
      case LetInEx( body, defs@_*) =>
        ( body +: (defs map {_.body}) ) flatMap allDiffs
      case _ =>
        Seq.empty
    }
}
