package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.types.smt.Z3TypeSolver.SolutionFunction

object SolutionInterpreter {
  type InterpretedSolution = Map[String, TlaType]

  /**
    * Intermediate type to be introduced by mkDelta, represents a type-mismatch between
    * two different instances of an operator application. Indicates that the operator
    * is polymorphic and its signature should use a type variable
    * instead of either the l-type or the r-type.
    */
  private sealed case class DeltaT( l : TlaType, r : TlaType ) extends TlaType

  /**
    * Resolving deltas, we can obtain `newType`, by replacing each instance of a delta
    * with the value specified by the substitution `deltaSub`.
    *
    * If mkDelta(a,b) returns DRR(t, sigma) and Delta(a_i,b_i) maps to T_i
    * in sigma, for all i, then a can be obtained by applying sigma' to t, where
    * sigma'(T_i) = a_i (analogous for b)
    */
  private sealed case class DeltaResolutionResult(
                                                   newType : TlaType,
                                                   deltaSub : Map[DeltaT, TlaType]
                                                 )

}

class SolutionInterpreter( tvg : TypeVarGenerator ) {

  import SolutionInterpreter._

  /**
    * Returns the types of all variables and generalized types of all operators
    */
  def interpret(
                 virtualCallResults : Map[String, TlaType],
                 bodyMap : BodyMap,
                 operCtx : OperatorContext,
                 globalNameCtx : GlobalNameContext,
                 solution : SolutionFunction
               ) : InterpretedSolution = {
    // For TLA variables, we just evaluate their matching SMT variables directly
    val varTypes = globalNameCtx map {
      case (varName, tv) => varName -> solution( tv )
    }

    // We construct an inverse UID->TlaEx mapping, so we know which UIDs belong to operator
    // application sites, in order to determine the types of operators. Simultaneously,
    // we also collect all the operator names from the BodyMap
    val (backMap, operNames) = bodyMap.foldLeft( (Map.empty[UID, TlaEx], Seq.empty[String]) ) {
      case ((partialMap, partialOpNames), (name, TlaOperDecl( _, _, body ))) =>
        (partialMap ++ aux.uidToExMap( body ), name +: partialOpNames)
    }

    // For each operator, we will look at its type
    // generalization, computed from the operator context
    // Some operator types are partially precomputed in virtualCallResults
    val operTypes = operNames map { opName =>
      opName -> generalizeType( opName, backMap, operCtx, solution, virtualCallResults )
    }

    varTypes ++ operTypes.toMap
  }

  /**
    * Given an operator name `operName`, computes the type generalization of all
    * application instances of `operName` across all possible contexts.
    * This gives us the polymorphic type of the operator `operName` (in this specification).
    *
    * If an operator appears in two different parts of the specification, with
    * types < X1, ... , Xn > => X0 and < Y1, ... , Yn > => Y0 where at least for one i
    * Xi != Yi, it must be the case that the type of the operator can be said to be
    * < Z1, ... , Zn > => Z0 where, for each i, Xi and Yi are particular instances of Zi
    *
    * Example:
    * The operator A has, at different locations, types < Int, Int > => Bool and
    * < Str, Str > => Bool. Generalization determines the type of A to be
    * < T0, T0 > => Bool. If we additionally know that an instance of A has type
    * < Int, Str > => Bool, the generalization becomes < T0, T1 > => Bool
    */
  def generalizeType(
                      operName : String,
                      idToExMap : Map[UID, TlaEx],
                      operCtx : OperatorContext,
                      solution : SolutionFunction,
                      virtualCallResults : Map[String, TlaType]
                    ) : TlaType = {
    // We gather every instance of operator application, from every possible
    // application stack. For each of them, `solution` gives us the type of that particular
    // instance.
    val allInstanceTypes = operCtx flatMap {
      case (_, asgn) => asgn flatMap {
        case (uid, tv) =>
          // It can happen that a key is not found in idToExMap. An example of this is
          // when, internally for type-constraints,
          // UNCHANGED a is transformed into a' = a. This intermediate
          // expression is ephemeral and as such is not recorded in idToExMap
          idToExMap.get( uid ) match {
            case Some( NameEx( n ) ) if n == operName =>
              Some( solution( tv ) )
            case _ => None
          }
      }
    }
    allInstanceTypes.toList match {
      case Nil =>
        // Only use virtual calls if there's no instance-use informaiton
        virtualCallResults.getOrElse( operName ,
          throw new Exception( s"Operator $operName should have at least one type candidate, but has 0." )
        )
      case head +: tail =>
        // We iteratively compute the polymorphic generalized type
        tail.foldLeft( head ) { case (t1, t2) => findPoly( t1, t2 ) }
    }
  }

  /**
    * Computes the type-delta (minimal incompatibility indicator) of two types
    */
  private def mkDelta( left : TlaType, right : TlaType ) : TlaType = (left, right) match {
    case (FunT( d1, c1 ), FunT( d2, c2 )) =>
      FunT( mkDelta( d1, d2 ), mkDelta( c1, c2 ) )
    case (SetT( s1 ), SetT( s2 )) =>
      SetT( mkDelta( s1, s2 ) )
    case (SeqT( s1 ), SeqT( s2 )) =>
      SeqT( mkDelta( s1, s2 ) )
    case (TupT( args1@_* ), TupT( args2@_* )) if args1.length == args2.length =>
      TupT( args1.zip( args2 ) map { case (l, r) => mkDelta( l, r ) } : _ * )
    case (RecT( tmap1 ), RecT( tmap2 )) =>
      val newMap = tmap1.keySet.intersect( tmap2.keySet ) map { k =>
        k -> mkDelta( tmap1( k ), tmap2( k ) )
      }
      RecT( newMap.toMap )
    case (SparseTupT( tmap1 ), SparseTupT( tmap2 )) =>
      val newMap = tmap1.keySet.intersect( tmap2.keySet ) map { k =>
        k -> mkDelta( tmap1( k ), tmap2( k ) )
      }
      SparseTupT( newMap.toMap )
    case (OperT( t1@TupT( args1@_* ), c1 ), OperT( t2@TupT( args2@_* ), c2 )) if args1.length == args2.length =>
      OperT( mkDelta( t1, t2 ).asInstanceOf[TupT], mkDelta( c1, c2 ) )
    case (x, y) if x == y => x
    case (x, y) => DeltaT( x, y )
  }

  /**
    * Computes the smallest (w.r.t. the number of type variables) polymorphic type t,
    * such that both `t1` and `t2` are instances of t and t preserves as much of the
    * syntactic form of t1/t2 as possible.
    */
  private def findPoly( t1 : TlaType, t2 : TlaType ) : TlaType =
    resolveDelta( mkDelta( t1, t2 ), Map.empty ).newType

  /**
    * Given a TlaType `tWithDelta`, possibly containing instances of `DeltaT`,
    * computes a new (polymorphic) type t, containing no deltas, such that
    * t can be obtained from `tWithDelta` by recursively applying the substitution`deltaSub`.
    *
    * The substitution `deltaSub` is minimal w.r.t. to the number of type variables introduced.
    */
  private def resolveDelta( tWithDelta : TlaType, deltaSub : Map[DeltaT, TlaType] ) : DeltaResolutionResult = tWithDelta match {
    case d : DeltaT =>
      deltaSub.get( d ) match {
        case None =>
          val newVar = tvg.getUnique
          DeltaResolutionResult( newVar, deltaSub + ( d -> newVar ) )
        case Some( v ) =>
          DeltaResolutionResult( v, deltaSub )
      }
    case FunT( dom, cdm ) =>
      val DeltaResolutionResult( newDom, newSub1 ) = resolveDelta( dom, deltaSub )
      val DeltaResolutionResult( newCdm, newSub2 ) = resolveDelta( cdm, newSub1 )
      DeltaResolutionResult( FunT( newDom, newCdm ), newSub2 )
    case SetT( s ) =>
      val r = resolveDelta( s, deltaSub )
      r.copy( newType = SetT( r.newType ) )
    case SeqT( s ) =>
      val r = resolveDelta( s, deltaSub )
      r.copy( newType = SeqT( r.newType ) )
    case TupT( args@_* ) =>
      val (newArgs, newDeltaSub) = args.foldRight( (List.empty[TlaType], deltaSub) ) {
        case (t, (partialArgs, partialDeltaSub)) =>
          val DeltaResolutionResult( newT, newPartialDeltaMap ) = resolveDelta( t, partialDeltaSub )
          (newT +: partialArgs, newPartialDeltaMap)
      }
      DeltaResolutionResult( TupT( newArgs : _* ), newDeltaSub )
    case RecT( tmap ) =>
      val (newTmap, newDeltaSub) = tmap.foldLeft( (Map.empty[String, TlaType], deltaSub) ) {
        case ((partialTmap, partialDeltaSub), (k, t)) =>
          val DeltaResolutionResult( newT, newPartialDeltaMap ) = resolveDelta( t, partialDeltaSub )
          (partialTmap + ( k -> newT ), newPartialDeltaMap)
      }
      DeltaResolutionResult( RecT( newTmap ), newDeltaSub )
    case SparseTupT( tmap ) =>
      val (newTmap, newDeltaSub) = tmap.foldLeft( (Map.empty[Int, TlaType], deltaSub) ) {
        case ((partialTmap, partialDeltaSub), (k, t)) =>
          val DeltaResolutionResult( newT, newPartialDeltaMap ) = resolveDelta( t, partialDeltaSub )
          (partialTmap + ( k -> newT ), newPartialDeltaMap)
      }
      DeltaResolutionResult( SparseTupT( newTmap ), newDeltaSub )
    case OperT( dom, cdm ) =>
      val DeltaResolutionResult( newDom, newSub1 ) = resolveDelta( dom, deltaSub )
      val DeltaResolutionResult( newCdm, newSub2 ) = resolveDelta( cdm, newSub1 )
      DeltaResolutionResult( OperT( newDom.asInstanceOf[TupT], newCdm ), newSub2 )
    // case PolyOperT should not happen
    case x => DeltaResolutionResult( x, deltaSub )
  }
}
