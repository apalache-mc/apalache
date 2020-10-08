package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.assignments.CoverData.ProblemData
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir._

import scala.collection.immutable.{Map, Set}

/**
  * Checks to see whether a specifications satisfies the covering property, i.e. whether
  * there exists at least one assignment candidate for each variable in `variables`
  * on each branch.
  */
class CoverChecker( allVariables: Set[String], manuallyAssigned: Set[String] = Set.empty ) {

  type letInOperBodyMapType = Map[String, CoverData]

  private def mkCoverInternal( initialLetInOperBodyMap : letInOperBodyMapType )
                           ( ex: TlaEx ): CoverData = ex match {
    /** Recursive case, connectives */
    case OperEx( oper, args@_* ) if oper == TlaBoolOper.and || oper == TlaBoolOper.or =>

      /** First, process children */
      val processedChildArgs : Seq[CoverData] =
        args.map( mkCoverInternal(initialLetInOperBodyMap) )

      /** Compute parent cover from children */

      if ( oper == TlaBoolOper.and )
        NonBranch( ex.ID, processedChildArgs:_* ) else
        BranchPoint( ex.ID, processedChildArgs : _* )


    /** Base case, assignment candidates */
    case OperEx( TlaOper.eq, OperEx( TlaActionOper.prime, NameEx( name ) ), star ) =>
      /** it's a candidate for name iff name \notin manuallyAssigned */
      if ( !manuallyAssigned.contains( name ) ) Candidate( name, ex.ID ) else NonCandidate( ex.ID )
    case OperEx( BmcOper.assign, OperEx( TlaActionOper.prime, NameEx( name ) ), star ) =>
      /** it's a candidate for name iff name \in manuallyAssigned */
      if ( manuallyAssigned.contains( name ) ) Candidate( name, ex.ID ) else NonCandidate( ex.ID )

    /** Recursive case, quantifier */
    case OperEx( TlaBoolOper.exists, NameEx( _ ), star, subEx ) =>
      mkCoverInternal( initialLetInOperBodyMap )( subEx )

    case OperEx( TlaControlOper.ifThenElse, star, thenExpr, elseExpr ) =>
      /** Recurse on both branches */
      val thenResults = mkCoverInternal( initialLetInOperBodyMap )(thenExpr)
      val elseResults = mkCoverInternal( initialLetInOperBodyMap )(elseExpr)

      /** Continue as with disjunction */
      BranchPoint( ex.ID,  thenResults, elseResults )

    /** Recursive case, nullary LetIn */
    case LetInEx( body, defs@_* ) =>
      // Sanity check, all operators must be nullary
      assert( defs.forall { _.formalParams.isEmpty } )
      /** First, analyze the bodies, to reuse later */
      val bodyResults = (defs map { d =>
        d.name -> mkCoverInternal( initialLetInOperBodyMap )( d.body )
      }).toMap

      /** Then, analyze the body, with the bodyResults map */
      mkCoverInternal( initialLetInOperBodyMap ++ bodyResults )( body )

    /** Nullary apply */
    case OperEx( TlaOper.apply, NameEx(operName) ) =>
      // Apply may appear in higher order operators, so it might not be possible to pre-analyze
      initialLetInOperBodyMap.getOrElse( operName, NonCandidate( ex.ID ) )

    /** In the other cases, return the default args */
    case _ => NonCandidate( ex.ID )
  }

  def mkCover( ex: TlaEx) : CoverData = {
    mkCoverInternal( Map.empty )(ex)
  }

  /** Computes the set of all variables, which are covered by `ex` */
  def coveredVars( ex: TlaEx ) : Set[String] = {
    val cd = mkCover(ex)

    val potentialProblemMap = (allVariables map {
      v => v -> CoverData.uncoveredBranchPoints( v )( cd )
    }).toMap


    potentialProblemMap.keySet.filter { k => potentialProblemMap(k).noProblem }

  }

  def findProblems( ex: TlaEx ): Option[Map[ String, ProblemData ]] = {
    val cd = mkCover(ex)

    val potentialProblemMap = (allVariables map {
      v => v -> CoverData.uncoveredBranchPoints( v )( cd )
    }).toMap


    val problemMap = potentialProblemMap.filter{ case (k,v) => !v.noProblem }

    if (problemMap.isEmpty) {
      None
    } else {
      Some( problemMap )
    }

  }
}
