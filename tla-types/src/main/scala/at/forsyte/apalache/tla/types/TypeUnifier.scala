package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.types.TypeComputer.Substitution

/**
  * EXPERIMENTAL, possibly redundant
  */

sealed case class AmbiguousType( ts : TlaType* ) extends TlaType

sealed case class UnificationResult( unifiedType: TlaType, substitution: Substitution )

class TypeUnifier {

  private def ambiguousUnify( t : TlaType, ts : Seq[TlaType] ) : Option[UnificationResult] = {
    val possibleUnif = ts flatMap { tl => unify( tl, t ) }

    // Maybe(?) the above unification created compatible types
    val selfCheck = for {
      (UnificationResult(p1, sub1), i) <- possibleUnif.zipWithIndex
      (UnificationResult(p2, sub2), j) <- possibleUnif.zipWithIndex
      newSub <- disjointMapMerge( sub1, sub2 )
      UnificationResult(u, sub3) <- if ( i <= j ) unify( p1, p2 ) else None
      finalSub <- disjointMapMerge( newSub, sub3 )
    } yield UnificationResult( u, finalSub )

    selfCheck match {
      case Nil => None
      case h +: Nil => Some( h )
      case _ =>
        possibleUnif.foldLeft( Option( Map.empty[Int, TlaType] ) ) {
          case ( partialSubOpt, UnificationResult( _, sub ) ) => for {
            partialSub <- partialSubOpt
            mergedSub <- disjointMapMerge( partialSub, sub )
          } yield mergedSub
        } map { sub =>
          UnificationResult( AmbiguousType( possibleUnif map { _.unifiedType } :_*), sub )
        }
    }
  }

  private def mapUnify[kType]( mapl : TypeMap[kType], mapr : TypeMap[kType] ) : Option[(TypeMap[kType], Substitution)] =
    ( mapl.keySet ++ mapr.keySet ).foldLeft( Option( (Map.empty[kType, TlaType], Map.empty[Int, TlaType] ) ) ) {
      case (pairOpt, k) =>
        for {
          (m, partialSub) <- pairOpt
          // If a value doesn't exist in one map,
          // we can take as the default the value from the other map.
          // Consequently, unify( x, x ) = x
          // If values exist in both maps, they must unify
          UnificationResult( v, sub ) <- unify(
            mapl.getOrElse( k, mapr( k ) ), // one of them must contain it
            mapr.getOrElse( k, mapl( k ) ) // mapX(_) is only evaluated in the Else banch
          )
          newSub <- disjointMapMerge( partialSub, sub )
        } yield (m + ( k -> v ), newSub)
    }

  def seekTVars( x : TlaType ) : Set[TypeVar] = x match {
    case tv : TypeVar => Set( tv )
    case FunT( d, c ) => seekTVars( d ) ++ seekTVars( c )
    case OperT( d, c ) => seekTVars( d ) ++ seekTVars( c )
    case SetT( s ) => seekTVars( s )
    case SeqT( s ) => seekTVars( s )
    case TupT( ts@_* ) => ts.foldLeft( Set.empty[TypeVar] ) {
      case (s, t) => s ++ seekTVars( t )
    }
    case SparseTupT( tmap ) => tmap.values.foldLeft( Set.empty[TypeVar] ) {
      case (s, t) => s ++ seekTVars( t )
    }
    case RecT( tmap ) => tmap.values.foldLeft( Set.empty[TypeVar] ) {
      case (s, t) => s ++ seekTVars( t )
    }
    case PolyOperT( _, o ) => seekTVars( o )
    case _ => Set.empty
  }

  def disjointMapMerge[K,V]( m1: Map[K,V], m2: Map[K,V] ) : Option[Map[K,V]] =
    if (m1.keySet.intersect(m2.keySet) forall {
      k => m1(k) == m2(k)
    }) Some(m1 ++ m2)
    else None

  def unify( l : TlaType, r : TlaType ) : Option[UnificationResult] = (l, r) match {
    case _ if l == r =>
      Some( UnificationResult( l, Map.empty ) )
    case (TypeVar( i ), tr) =>
      Some( UnificationResult( tr, Map( i -> tr ) ) )
    case (tl, TypeVar( i )) =>
      Some( UnificationResult( tl, Map( i -> tl ) ) )
    case (FunT( domL, cdmL ), FunT( domR, cdmR )) => for {
      UnificationResult(uDom, subDom) <- unify( domL, domR )
      UnificationResult(uCdm, subCdm) <- unify( cdmL, cdmR )
      sub <- disjointMapMerge(subDom, subCdm)
    } yield UnificationResult( FunT( uDom, uCdm ), sub)
    case (OperT( domL, cdmL ), OperT( domR, cdmR )) =>
      val tupOpt = for {
        UnificationResult(uDom, subDom) <- unify( domL, domR )
        UnificationResult(uCdm, subCdm) <- unify( cdmL, cdmR )
        sub <- disjointMapMerge(subDom, subCdm)
      } yield ( uDom, uCdm, sub)
      tupOpt match {
        case Some( (tt : TupT, c, sub) ) =>
          Some( UnificationResult( OperT( tt, c ), sub ) )
        case _ => None
      }
    case (PolyOperT( _, opl ), PolyOperT( _, opr )) =>
      unify( opl, opr ) flatMap {
        case r@UnificationResult( op : OperT, sub ) => seekTVars( op ).toList match {
          case Nil => Some( r )
          case ls => Some( UnificationResult( PolyOperT( ls, op ), sub ) )
        }
        case _ => None
      }
    case (pol : PolyOperT, opl : OperT) => unify( pol, PolyOperT( List.empty, opl ) )
    case (opl : OperT, por : PolyOperT) => unify( PolyOperT( List.empty, opl ), por )
    case (SetT( tl ), SetT( tr )) =>
      unify( tl, tr ) map {
        case UnificationResult( t, sub ) => UnificationResult( SetT(t), sub )
      }
    case (SeqT( tl ), SeqT( tr )) =>
      unify( tl, tr ) map {
        case UnificationResult( t, sub ) => UnificationResult( SeqT(t), sub )
      }
    case (TupT( tsl@_* ), TupT( tsr@_* )) =>
      if ( tsl.length != tsr.length )
        None
      else
        tsl.zip( tsr ).foldRight( Option( (Seq.empty[TlaType], Map.empty[Int, TlaType]) ) ) {
          case ((tl, tr), pairOpt) => for {
            (seq, partialSub) <- pairOpt
            UnificationResult(u, sub) <- unify( tl, tr )
            newSub <- disjointMapMerge( partialSub, sub )
          } yield (u +: seq, newSub)
        } map {
          case ( tupArgs, sub ) => UnificationResult( TupT( tupArgs : _* ), sub )
        }
    case (TupT( tsl@_* ), SparseTupT( mapr )) =>
      unifyTuples( mapr, tsl )
    case (SparseTupT( mapl ), TupT( tsr@_* )) =>
      unifyTuples( mapl, tsr )
    case (SparseTupT( mapl ), SparseTupT( mapr )) =>
      mapUnify[Int]( mapl, mapr ) map {
        case (m, sub) => UnificationResult( SparseTupT( m ), sub )
      }
    case (RecT( mapl ), RecT( mapr )) =>
      mapUnify[String]( mapl, mapr ) map {
        case (m, sub) => UnificationResult( RecT( m ), sub )
      }
    case (AmbiguousType( tsl@_* ), tr) =>
      ambiguousUnify( tr, tsl )
    case (tl, AmbiguousType( tsr@_* )) =>
      ambiguousUnify( tl, tsr )
    case _ => None
  }

  def unifyTuples( sparseTupMap : TypeMap[Int], tupArgs : Seq[TlaType] ) : Option[UnificationResult] = {
    val tupSize = tupArgs.length
    val sparseTupTooBig = sparseTupMap.keySet.exists { k =>
      k >= tupSize
    }
    if ( sparseTupTooBig ) None
    else tupArgs.zipWithIndex.foldRight( Option( (Seq.empty[TlaType], Map.empty[Int, TlaType] ) ) ) {
      case ((t, i), pairOpt) => for {
        (seq, partialSub) <- pairOpt
        UnificationResult(newT, sub) <- unify( t, sparseTupMap.getOrElse( i, t ) )
        newSub <- disjointMapMerge( partialSub, sub)
      } yield (newT +: seq, newSub )
    } map {
      case ( seq, sub ) => UnificationResult( TupT( seq : _* ), sub )
    }
  }

}
