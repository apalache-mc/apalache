package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.UID

/**
  * CoveringData is a tree structure, detailing branch points in a TLA+ specification.
  * Each ITE or \/, not belonging to a star-expression, constitutes a branch-point, i.e.
  * each of its child-expressions will belong to a different branch.
  */
class CoverData( uid: UID )
sealed case class BranchPoint( uid: UID, branches: CoverData* ) extends CoverData(uid)
sealed case class NonBranch( uid: UID, elements: CoverData* ) extends CoverData(uid)
sealed case class Candidate( varName: String, uid: UID ) extends CoverData(uid)
sealed case class NonCandidate( uid: UID ) extends CoverData(uid)

object CoverData{

  class CoverException( s : String ) extends Exception( s )

  class IncompleteCover(seq: Seq[UID]) {
    def get: Seq[UID] = seq
    def isEmpty: Boolean = seq.isEmpty
  }
  sealed case class AtLeastOne( seq: Seq[UID] ) extends IncompleteCover(seq)
  sealed case class All( seq: Seq[UID] ) extends IncompleteCover(seq)
  sealed case class NoProblem() extends IncompleteCover( Seq.empty )

  /**
    * ProblemData represents potential witnesses to cover violations.
    * The collection `problemUIDs` lists the largest subexpressions (by UID), which
    * witness cover violation, relative to the expression from which ProblemData
    * is computed. The map `blameMap` allows us to find more fine-grained violations;
    * if a value k in `problemUIDs` is a key in `blameMap`, a value v, that k maps to, is
    * the value of `problemUIDs`, taking the expression corresponding to k
    * as the root of computation.
    */
  sealed case class ProblemData(
                                 problemUIDs: IncompleteCover,
                                 blameMap: Map[UID, IncompleteCover]
                               ) {
    /** Checks if any witnesses exist */
    def noProblem: Boolean = problemUIDs.isEmpty && blameMap.isEmpty

    /**
      * If an expression e labeled with `uid` is a witness, we can attempt to
      * find a subexpression of e, which is a "better" (smaller) witness,
      * by tracing `blameMap`
      */
    def focusOn( uid: UID ): Option[ProblemData] =
        blameMap.get( uid ) map { ic =>
          ProblemData( ic, blameMap )
        }

    /**
      * Enumerates all possible ways to refine witnesses.
      */
    def focusCandidates: Seq[ProblemData] = problemUIDs.get flatMap focusOn

  }

  def uncoveredBranchPoints( varName: String )( cd: CoverData ) : ProblemData = cd match {
    case Candidate( v, loc ) =>
      // Candidate(v, _) covers varName iff v == varName
      val problem = if ( varName == v ) NoProblem() else AtLeastOne( Seq( loc ) )
      ProblemData( problem, Map.empty )
    case NonCandidate( loc ) =>
      // NonCandidate never covers varname, but is also a leaf in blameMap
      ProblemData( AtLeastOne( Seq( loc ) ), Map.empty )
    case BranchPoint( loc, branches@_* ) =>
      // BranchPoint represents disjunction/ITE, so it covers varName iff
      // *all* disjuncts/ITE branches cover varName
      val branchIssues =
        branches.foldLeft( ProblemData( NoProblem(), Map.empty ) ) {
          case (pd,brCd) =>
            val brPd = uncoveredBranchPoints( varName )( brCd )
            ProblemData(
              All( pd.problemUIDs.get ++ brPd.problemUIDs.get ),
              pd.blameMap ++ brPd.blameMap
            )
        }

      if (!branchIssues.problemUIDs.isEmpty){
        // If a subexpression contains a cover violation the BranchPoint sets itself
        // as a problem location and pushes the subexpression issues into blameMap
        ProblemData(
          All( Seq( loc ) ),
          branchIssues.blameMap + ( loc -> branchIssues.problemUIDs )
        )
      } else {
        branchIssues
      }

    case NonBranch( loc, elements@_* ) =>
      // NonBranch corresponds to conjunction, so it covers varName if any of its
      // subexpressions cover varName
      val elemIssues = elements map uncoveredBranchPoints( varName )
      if ( elemIssues.exists( _.problemUIDs.isEmpty ) ) {
        // If a suitable cover is found, report NoProblem
        ProblemData( NoProblem(), Map.empty )
      } else {
        // Otherwise, no sub-expression covers varName, so we aggregate all sub-locations
        val problemAggregate = elemIssues.foldLeft( ProblemData( NoProblem(), Map.empty ) ) {
          case (pd,brPd) =>
            ProblemData(
              AtLeastOne( pd.problemUIDs.get ++ brPd.problemUIDs.get),
              pd.blameMap ++ brPd.blameMap
            )
        }
        // Then, NonBranch sets itself as a problem location, as in the previous case
        ProblemData(
          AtLeastOne( Seq( loc ) ),
          problemAggregate.blameMap + ( loc -> problemAggregate.problemUIDs )
        )
      }
  }

}