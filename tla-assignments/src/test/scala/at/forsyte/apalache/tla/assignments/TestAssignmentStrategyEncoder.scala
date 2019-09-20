package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.{TestingPredefs, TlaEx}
import at.forsyte.apalache.tla.lir.Builder._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.Set

@RunWith( classOf[JUnitRunner] )
class TestAssignmentStrategyEncoder extends FunSuite with TestingPredefs {

  import AssignmentStrategyEncoder._
  import at.forsyte.apalache.tla.assignments.SmtTools._

  val encoder = new AssignmentStrategyEncoder()

  def analyze( phi : TlaEx, vars : Set[String] ) : StaticAnalysisData =
    encoder.staticAnalysis( phi, vars, Set[String](), Map.empty[String, StaticAnalysisData] )

  val vars = Set( "x", "y" )
  val defaultVarsDelta = (vars map {x => x -> False()}).toMap

  test( "Test staticAnalysis: star" ) {
    val nameEx = n_x
    val nameExSAD = analyze( nameEx, vars )

    assert( nameExSAD ==
      StaticAnalysisData(
        Set.empty,
        Set.empty,
        Set.empty,
        defaultVarsDelta,
        Map.empty,
        Map.empty
      )
    )
    assert( nameExSAD.simplified.delta == nameExSAD.delta )
  }

  test( "Test staticAnalysis: assignment" ) {
    val asgn = primeInSingleton( n_x, int( 1 ) )
    val asgnSAD = analyze( asgn, vars )

    assert( asgnSAD ==
      StaticAnalysisData(
        Set( asgn.ID.id ),
        Set( (asgn.ID.id, asgn.ID.id) ),
        Set.empty[(Long, Long)],
        Map( "x" -> Variable( asgn.ID.id ), "y" -> False() ),
        Map( asgn.ID.id -> Set.empty[String] ),
        Map( asgn.ID.id -> asgn )
      )
    )
    assert( asgnSAD.simplified.delta == asgnSAD.delta )
  }
  test( "Test staticAnalysis: or" ) {

    val asgnX1 = primeInSingleton( n_x, int( 1 ) )
    val asgnX2 = primeInSingleton( n_x, int( 2 ) )
    val cmpX1 = eql( n_x, int( 1 ) )
    val cmpX2 = eql( n_x, int( 2 ) )

    val balancedOr = or( asgnX1, asgnX2 )
    val imbalancedOr = or( asgnX1, cmpX1 )
    val conditionOr = or( cmpX1, cmpX2 )

    val balancedOrSAD = analyze( balancedOr, vars )

    assert( balancedOrSAD ==
      StaticAnalysisData(
        Set( asgnX1.ID.id, asgnX2.ID.id ),
        Set( (asgnX1.ID.id, asgnX1.ID.id), (asgnX2.ID.id, asgnX2.ID.id) ),
        Set( (asgnX1.ID.id, asgnX2.ID.id), (asgnX2.ID.id, asgnX1.ID.id) ),
        Map( "x" -> And( Variable( asgnX1.ID.id ), Variable( asgnX2.ID.id ) ), "y" -> And( False(), False() ) ),
        Map( asgnX1.ID.id -> Set.empty[String], asgnX2.ID.id -> Set.empty[String] ),
        Map( asgnX1.ID.id -> asgnX1, asgnX2.ID.id -> asgnX2 )
      )
    )
    assert(
      balancedOrSAD.simplified.delta ==
        Map( "x" -> And( Variable( asgnX1.ID.id ), Variable( asgnX2.ID.id ) ), "y" -> False() )
    )

    val imbalancedOrSAD = analyze( imbalancedOr, vars )

    assert( imbalancedOrSAD ==
      StaticAnalysisData(
        Set( asgnX1.ID.id ),
        Set( (asgnX1.ID.id, asgnX1.ID.id) ),
        Set.empty,
        Map( "x" -> And( Variable( asgnX1.ID.id ), False() ), "y" -> And( False(), False() ) ),
        Map( asgnX1.ID.id -> Set.empty[String] ),
        Map( asgnX1.ID.id -> asgnX1 )
      )
    )
    assert( imbalancedOrSAD.simplified.delta == defaultVarsDelta )

    val conditionOrSAD = analyze( conditionOr, vars )

    assert( conditionOrSAD ==
      StaticAnalysisData(
        Set.empty,
        Set.empty,
        Set.empty,
        Map( "x" -> And( False(), False() ), "y" -> And( False(), False() ) ),
        Map.empty,
        Map.empty
      )
    )
    assert( conditionOrSAD.simplified.delta == defaultVarsDelta )
  }

  test( "Test staticAnalysis: and" ) {

    val asgnX = primeInSingleton( n_x, int( 1 ) )
    val asgnY = primeInSingleton( n_y, int( 1 ) )
    val andAsgns = and( asgnX, asgnY )
    val andAsgnsSAD = analyze( andAsgns, vars )

    assert( andAsgnsSAD ==
      StaticAnalysisData(
        Set( asgnX.ID.id, asgnY.ID.id ),
        Set( (asgnX.ID.id, asgnX.ID.id), (asgnY.ID.id, asgnY.ID.id), (asgnX.ID.id, asgnY.ID.id), (asgnY.ID.id, asgnX.ID.id) ),
        Set.empty,
        Map( "x" -> Or( Variable( asgnX.ID.id ), False() ), "y" -> Or( False(), Variable( asgnY.ID.id ) ) ),
        Map( asgnX.ID.id -> Set.empty[String], asgnY.ID.id -> Set.empty[String] ),
        Map( asgnX.ID.id -> asgnX, asgnY.ID.id -> asgnY )
      )
    )
    assert( andAsgnsSAD.simplified.delta == Map( "x" -> Variable( asgnX.ID.id ), "y" -> Variable( asgnY.ID.id ) ) )

    val cmpY = eql( n_y, int( 1 ) )
    val andCmp = and( asgnX, cmpY )
  }

}
