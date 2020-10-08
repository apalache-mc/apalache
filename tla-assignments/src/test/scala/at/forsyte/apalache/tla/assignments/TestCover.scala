package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.{TestingPredefs, UID}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner


@RunWith( classOf[JUnitRunner] )
class TestCover extends FunSuite with TestingPredefs {

  test( "Basic case: OK" ) {
    val varName = "x"
    val cd : CoverData = BranchPoint(
      UID.unique,
      NonBranch(
        UID.unique,
        Candidate( varName, UID.unique ),
        Candidate( varName, UID.unique )
      ),
      Candidate( varName, UID.unique )
    )

    assert( CoverData.uncoveredBranchPoints( varName )( cd ).noProblem )
  }

  test( "Basic case: Problem" ) {
    val varName = "x"
    val branchId = UID.unique
    val nonCandId = UID.unique
    val cd : CoverData = BranchPoint(
      branchId,
      NonBranch(
        UID.unique,
        Candidate( varName, UID.unique ),
        Candidate( varName, UID.unique )
      ),
      NonCandidate( nonCandId )
    )

    val uncovered = CoverData.uncoveredBranchPoints( varName )( cd )

    assert( !uncovered.noProblem )

    assert( uncovered.problemUIDs == Seq( branchId ) )
    assert( uncovered.blameMap( branchId ) == Seq( nonCandId ) )

  }


  test( "Problem on 2 branches" ) {
    val varName = "x"
    val topId = UID.unique
    val cd : CoverData = NonBranch(
      topId,
      BranchPoint(
        UID.unique,
        Candidate( varName, UID.unique ),
        NonCandidate( UID.unique )
      ),
      BranchPoint(
        UID.unique,
        Candidate( varName, UID.unique ),
        NonCandidate( UID.unique )
      )
    )

    val uncovered = CoverData.uncoveredBranchPoints( varName )( cd )

    assert( !uncovered.noProblem )

    assert( uncovered.problemUIDs == Seq( topId ) )
    assert( uncovered.blameMap( topId ).get.length == 2 )

  }

  test( "FromEx" ) {
    val ex = tla.or(
      tla.primeEq( n_x, 1 ),
      tla.primeEq( n_x, 2 )
    )

    val checker = new CoverChecker( Set( "x" ) )
    val cover = checker.mkCover( ex )

    assert( CoverData.uncoveredBranchPoints( "x" )( cover ).noProblem )

  }

  test( "FromEx : cplx" ) {

    val problem = tla.eql( n_x, 3 )
    val ex = tla.or(
      tla.and(
        tla.primeEq( n_x, 1 ),
        tla.primeEq( n_y, 1 )
      ),
      tla.and(
        tla.primeEq( n_x, 2 ),
        tla.primeEq( n_y, 2 )
      ),
      tla.and(
        problem, // not a candidate
        tla.primeEq( n_y, 3 )
      ),
      tla.and(
        tla.primeEq( n_x, 4 ),
        tla.primeEq( n_y, 4 )
      )
    )

    val vars = Set( "x", "y" )

    val checker = new CoverChecker( vars )
    val cover = checker.mkCover( ex )

    assert( CoverData.uncoveredBranchPoints( "y" )( cover ).noProblem )

    val xProblems = CoverData.uncoveredBranchPoints( "x" )( cover )

    assert( !xProblems.noProblem )
  }


}

