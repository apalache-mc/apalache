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
                                 problemUIDs: Seq[UID],
                                 blameMap: Map[UID, Seq[UID]]
                               ) {
    /** Checks if any witnesses exist */
    def noProblem: Boolean = problemUIDs.isEmpty && blameMap.isEmpty

    /**
      * If an expression e labeled with `uid` is a witness, we can attempt to
      * find a subexpression of e, which is a "better" (smaller) witness,
      * by tracing `blameMap`
      */
    def focusOn( uid: UID ): Option[ProblemData] =
        blameMap.get( uid ) map { seq =>
          ProblemData( seq, blameMap )
        }

    /**
      * Enumerates all possible ways to refine witnesses.
      */
    def focusCandidates: Seq[ProblemData] = problemUIDs flatMap focusOn

    /**
      * Corrects all groups of expressions, where at least one is expected
      * to be an assignment candidate
      */
    def allProblemLeaves: Seq[Seq[UID]] = {
      val cand = focusCandidates
      if (cand.isEmpty) Seq(problemUIDs)
      else cand flatMap {_.allProblemLeaves}
    }
  }

  def uncoveredBranchPoints( varName: String )( cd: CoverData ) : ProblemData = cd match {
    case Candidate( v, loc ) =>
      val problem = if ( varName == v ) Seq.empty else Seq( loc )
      ProblemData( problem, Map.empty )
    case NonCandidate( loc ) => ProblemData( Seq( loc ), Map.empty )
    case BranchPoint( loc, branches@_* ) =>
      val branchIssues =
        branches.foldLeft( ProblemData( Seq.empty, Map.empty ) ) {
          case (pd,brCd) =>
            val brPd = uncoveredBranchPoints( varName )( brCd )
            ProblemData(
              pd.problemUIDs ++ brPd.problemUIDs,
              pd.blameMap ++ brPd.blameMap
            )
        }

      if (branchIssues.problemUIDs.nonEmpty){
        ProblemData(
          Seq( loc ),
          branchIssues.blameMap + ( loc -> branchIssues.problemUIDs )
        )
      } else {
        branchIssues
      }

    case NonBranch( loc, elements@_* ) =>
      val elemIssues = elements map uncoveredBranchPoints( varName )
      if ( elemIssues.exists( _.problemUIDs.isEmpty ) ) {
        ProblemData( Seq.empty, Map.empty )
      } else {
        val problemAggregate = elemIssues.foldLeft( ProblemData( Seq.empty, Map.empty ) ) {
          case (pd,brPd) =>
            ProblemData(
              pd.problemUIDs ++ brPd.problemUIDs,
              pd.blameMap ++ brPd.blameMap
            )
        }
        ProblemData(
          Seq( loc ),
          problemAggregate.blameMap + ( loc -> problemAggregate.problemUIDs )
        )
      }
  }
}