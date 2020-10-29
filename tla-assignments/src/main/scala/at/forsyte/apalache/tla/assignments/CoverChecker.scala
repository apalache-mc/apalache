package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.storage.BodyMap

import scala.collection.immutable.{Map, Set}

/**
  * Checks to see whether a specifications satisfies the covering property, i.e. whether
  * there exists at least one assignment candidate for each variable in `variables`
  * on each branch.
  */
class CoverChecker( allVariables: Set[String], manuallyAssigned: Set[String] = Set.empty ) {


  type operCoverMapType = Map[String, CoverData]

  def mkCover( bodyMap: BodyMap ) : operCoverMapType = bodyMap.values.foldLeft( Map.empty[String,CoverData] ){
    case (partialMap, TlaOperDecl( opName, _, opBody)) =>
      val (opCover, sideComputedMap) = mkCoverInternal( bodyMap, partialMap, Map.empty )( opBody )
      sideComputedMap + ( opName -> opCover )
  }

  def mkCoverEx( bodyMap : BodyMap )( ex : TlaEx, initialCoverMap : operCoverMapType = Map.empty ) : CoverData =
    mkCoverInternal( bodyMap, initialCoverMap, Map.empty )( ex )._1

  private def mkCoverInternal(
                               bodyMap : BodyMap,
                               initialOperMap : operCoverMapType,
                               initialLetInOperBodyMap : operCoverMapType
                             )
                             ( ex: TlaEx ): (CoverData,operCoverMapType)  = ex match {
    /** Recursive case, connectives */
    case OperEx( oper, args@_* ) if oper == TlaBoolOper.and || oper == TlaBoolOper.or =>

      /** First, process children */
      val processedChildArgs : Seq[(CoverData, operCoverMapType)] =
        args.map( mkCoverInternal( bodyMap, initialOperMap, initialLetInOperBodyMap ) )

      val (childCover,newSideComputedMap) = processedChildArgs.foldLeft( Seq.empty[CoverData], initialOperMap ){
        case ((partialChildren, partialMap), (coverData, map) ) =>
          (partialChildren :+ coverData, partialMap ++ map)
      }

      /** Compute parent cover from children */
      val parentCover = if ( oper == TlaBoolOper.and )
        NonBranch( ex.ID, childCover:_* ) else
        BranchPoint( ex.ID, childCover : _* )

      (parentCover, newSideComputedMap)

    /** Base case, assignment candidates */
    case OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, NameEx( name ) ), _ ) =>
      /** it's a candidate for name iff name \notin manuallyAssigned */
      val cover = if ( !manuallyAssigned.contains( name ) ) Candidate( name, ex.ID ) else NonCandidate( ex.ID )
      (cover, initialOperMap)

    case OperEx( BmcOper.assign, OperEx( TlaActionOper.prime, NameEx( name ) ), _ ) =>
      /** it's a candidate for name iff name \in manuallyAssigned */
      val cover = if ( manuallyAssigned.contains( name ) ) Candidate( name, ex.ID ) else NonCandidate( ex.ID )
      (cover, initialOperMap)

    /** Recursive case, quantifier */
    case OperEx( TlaBoolOper.exists, NameEx( _ ), _, subEx ) =>
      mkCoverInternal( bodyMap, initialOperMap, initialLetInOperBodyMap )( subEx )

    case OperEx( TlaControlOper.ifThenElse, _, thenExpr, elseExpr ) =>
      /** Recurse on both branches */
      val (thenCover, thenMap) = mkCoverInternal( bodyMap, initialOperMap, initialLetInOperBodyMap )( thenExpr )
      val (elseCover, elseMap) = mkCoverInternal( bodyMap, initialOperMap, initialLetInOperBodyMap )( elseExpr )

      /** Continue as with disjunction */
      val cover = BranchPoint( ex.ID,  thenCover, elseCover )
      (cover, thenMap  ++ elseMap)

    /** Recursive case, nullary LetIn */
    case LetInEx( body, defs@_* ) =>
      // Sanity check, all operators must be nullary
      assert( defs.forall { _.formalParams.isEmpty } )
      /** First, analyze the bodies, to reuse later */
      val (newLetInMap, sideComputedMap) = defs.foldLeft( initialLetInOperBodyMap, initialOperMap ) {
        case ((partialLetInMap, partialSideComputation), TlaOperDecl( letInDeclName, _, letInDeclbody )) =>
          val (cover, newSideComputedMap) =
            mkCoverInternal( bodyMap, partialSideComputation, partialLetInMap )( letInDeclbody )
          (partialLetInMap + ( letInDeclName -> cover ), newSideComputedMap)
      }

      /** Then, analyze the body, with the bodyResults map */
      mkCoverInternal( bodyMap, sideComputedMap, newLetInMap )( body )

    /** Application case, user-defined top-level operator */
    case OperEx( TlaOper.apply, NameEx(operName), _* ) if bodyMap.contains( operName ) =>
      // Assignments cannot appear in arguments to an operator, so we can ignore those

      // We can sometimes leverage memoization:
      val preComputedOpt = initialOperMap.get( operName )
      if (preComputedOpt.nonEmpty)
        (preComputedOpt.get, initialOperMap)
      else {
        // If not, we compute the cover and store it
        val opBody = bodyMap( operName ).body
        val (cover, sideComputedMap) = mkCoverInternal( bodyMap, initialOperMap, initialLetInOperBodyMap )( opBody )
        (cover, sideComputedMap + (operName -> cover))
      }


    /** Other apply */
    case OperEx( TlaOper.apply, NameEx(operName) ) =>
      // Apply may appear in higher order operators, so it might not be possible to pre-analyze
      val cover = initialLetInOperBodyMap.getOrElse( operName, NonCandidate( ex.ID ) )
      (cover, initialOperMap)

    /** In the other cases, return the default args */
    case _ => (NonCandidate( ex.ID ), initialOperMap)
  }


//  private def mkCoverInternal2( initialLetInOperBodyMap : operCoverMapType )
//                           ( ex: TlaEx ): CoverData = ex match {
//    /** Recursive case, connectives */
//    case OperEx( oper, args@_* ) if oper == TlaBoolOper.and || oper == TlaBoolOper.or =>
//
//      /** First, process children */
//      val processedChildArgs : Seq[CoverData] =
//        args.map( mkCoverInternal2(initialLetInOperBodyMap) )
//
//      /** Compute parent cover from children */
//
//      if ( oper == TlaBoolOper.and )
//        NonBranch( ex.ID, processedChildArgs:_* ) else
//        BranchPoint( ex.ID, processedChildArgs : _* )
//
//
//    /** Base case, assignment candidates */
//    case OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, NameEx( name ) ), star ) =>
//      /** it's a candidate for name iff name \notin manuallyAssigned */
//      if ( !manuallyAssigned.contains( name ) ) Candidate( name, ex.ID ) else NonCandidate( ex.ID )
//    case OperEx( BmcOper.assign, OperEx( TlaActionOper.prime, NameEx( name ) ), star ) =>
//      /** it's a candidate for name iff name \in manuallyAssigned */
//      if ( manuallyAssigned.contains( name ) ) Candidate( name, ex.ID ) else NonCandidate( ex.ID )
//
//    /** Recursive case, quantifier */
//    case OperEx( TlaBoolOper.exists, NameEx( _ ), star, subEx ) =>
//      mkCoverInternal2( initialLetInOperBodyMap )( subEx )
//
//    case OperEx( TlaControlOper.ifThenElse, star, thenExpr, elseExpr ) =>
//      /** Recurse on both branches */
//      val thenResults = mkCoverInternal2( initialLetInOperBodyMap )(thenExpr)
//      val elseResults = mkCoverInternal2( initialLetInOperBodyMap )(elseExpr)
//
//      /** Continue as with disjunction */
//      BranchPoint( ex.ID,  thenResults, elseResults )
//
//    /** Recursive case, nullary LetIn */
//    case LetInEx( body, defs@_* ) =>
//      // Sanity check, all operators must be nullary
//      assert( defs.forall { _.formalParams.isEmpty } )
//      /** First, analyze the bodies, to reuse later */
//      val bodyResults = (defs map { d =>
//        d.name -> mkCoverInternal2( initialLetInOperBodyMap )( d.body )
//      }).toMap
//
//      /** Then, analyze the body, with the bodyResults map */
//      mkCoverInternal2( initialLetInOperBodyMap ++ bodyResults )( body )
//
//    /** Nullary apply */
//    case OperEx( TlaOper.apply, NameEx(operName) ) =>
//      // Apply may appear in higher order operators, so it might not be possible to pre-analyze
//      initialLetInOperBodyMap.getOrElse( operName, NonCandidate( ex.ID ) )
//
//    /** In the other cases, return the default args */
//    case _ => NonCandidate( ex.ID )
//  }
//
//  def mkCover2( ex: TlaEx) : CoverData = {
//    mkCoverInternal2( Map.empty )(ex)
//  }

  /** Computes the set of all variables, which are covered by each operator */
  def coveredVars( coverMap: operCoverMapType ) : Map[ String, Set[String]] = {
    coverMap map {
      case (opName, cover) => opName ->
        allVariables.filter(
          v => CoverData.uncoveredBranchPoints( v )( cover ).noProblem
        )
    }

  }

  /** Computes a set of assignment candidates under each operator */
  def assignmentLocaitons( coverMap: operCoverMapType ) : Map[String, Set[Candidate]] =
    coverMap map {
      case (opName, cover) => opName ->
        allVariables.flatMap(
          v => CoverData.uncoveredBranchPoints( v )( cover ).problemUIDs.asgns
        )

  }

}
