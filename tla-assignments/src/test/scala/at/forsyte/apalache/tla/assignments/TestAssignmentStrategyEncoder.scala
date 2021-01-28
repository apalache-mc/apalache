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
  import at.forsyte.apalache.tla.lir.smt.SmtTools._

  val encoder = new AssignmentStrategyEncoder()

  def analyze( phi : TlaEx, vars : Set[String] ) : StaticAnalysisData =
    encoder.staticAnalysis( phi, vars, Set[String](), Map.empty[String, StaticAnalysisData], Set.empty )

  // We make a custom assert, so that if/when it fails, we can more easily identify the problematic field
  def assertEqualSAD( a: StaticAnalysisData, b: StaticAnalysisData ): Unit = {
    assert( a.seen == b.seen )
    assert( a.collocSet == b.collocSet )
    assert( a.nonCollocSet == b.nonCollocSet )
    assert( a.delta == b.delta )
    assert( a.frozen == b.frozen )
    assert( a.uidToExmap == b.uidToExmap)
  }

  val vars = Set( "x", "y" )
  val defaultVarsDelta = (vars map {x => x -> False()}).toMap
  val defaultEmptySAD = StaticAnalysisData(
    Set.empty,
    Set.empty,
    Set.empty,
    defaultVarsDelta,
    Map.empty,
    Map.empty
  )

  test( "Test staticAnalysis: star" ) {
    val nameEx = n_x
    val nameExSAD = analyze( nameEx, vars )

    assertEqualSAD( nameExSAD, defaultEmptySAD )
    assert( nameExSAD.simplified.delta == nameExSAD.delta )
  }

  test( "Test staticAnalysis: assignment" ) {
    val asgn = primeEq( n_x, int( 1 ) )
    val asgnSAD = analyze( asgn, vars )

    assertEqualSAD( asgnSAD,
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

    val asgnX1 = primeEq( n_x, int( 1 ) )
    val asgnX2 = primeEq( n_x, int( 2 ) )
    val cmpX1 = eql( n_x, int( 1 ) )
    val cmpX2 = eql( n_x, int( 2 ) )

    val balancedOr = or( asgnX1, asgnX2 )
    val imbalancedOr = or( asgnX1, cmpX1 )
    val conditionOr = or( cmpX1, cmpX2 )

    val balancedOrSAD = analyze( balancedOr, vars )

    assertEqualSAD( balancedOrSAD,
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

    assertEqualSAD( imbalancedOrSAD,
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

    assertEqualSAD( conditionOrSAD,
      defaultEmptySAD.copy(
        delta = Map( "x" -> And( False(), False() ), "y" -> And( False(), False() ) )
      )
    )
    assert( conditionOrSAD.simplified.delta == defaultVarsDelta )
  }

  test( "Test staticAnalysis: and" ) {

    val asgnX = primeEq( n_x, int( 1 ) )
    val asgnY = primeEq( n_y, int( 1 ) )
    val cmpX = eql( n_x, int( 1 ) )
    val cmpY = eql( n_y, int( 1 ) )

    val andAsgns = and( asgnX, asgnY )
    val andMixed1 = and( asgnX, cmpX )
    val andMixed2 = and( asgnX, cmpY )
    val andCmp = and( cmpX, cmpY )

    val andAsgnsSAD = analyze( andAsgns, vars )

    assertEqualSAD( andAsgnsSAD,
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

    val andMixed1SAD = analyze( andMixed1, vars )

    assertEqualSAD( andMixed1SAD,
      StaticAnalysisData(
        Set( asgnX.ID.id ),
        Set( (asgnX.ID.id, asgnX.ID.id) ),
        Set.empty,
        Map( "x" -> Or( Variable( asgnX.ID.id ), False() ), "y" -> Or( False(), False() ) ),
        Map( asgnX.ID.id -> Set.empty[String] ),
        Map( asgnX.ID.id -> asgnX )
      )
    )
    assert( andMixed1SAD.simplified.delta == Map( "x" -> Variable( asgnX.ID.id ), "y" -> False() ) )

    val andMixed2SAD = analyze( andMixed2, vars )

    assertEqualSAD( andMixed1SAD, andMixed2SAD )

    val andCmpSAD = analyze( andCmp, vars )

    assertEqualSAD( andCmpSAD,
      defaultEmptySAD.copy(
        delta = Map( "x" -> Or( False(), False() ), "y" -> Or( False(), False() ) )
      )
    )
    assert( andCmpSAD.simplified.delta == defaultVarsDelta )

  }

  test( "Test staticAnalysis: exists" ){
    val asgn = primeEq( n_x, n_z )
    val cmp = eql( n_x, n_z )
    val existsAsgn = exists( n_z, enumSet( prime( n_y ) ), asgn )
    val existsDoubleAsgn = exists( n_z, enumSet( prime( n_y ) ), exists (n_t, emptySet(), asgn ) )
    val existsCmp = exists( n_z, enumSet( prime( n_y ) ), cmp )
    val existsDoubleCmp = exists( n_z, enumSet( prime( n_y ) ), exists (n_t, emptySet(), cmp ) )

    val existsAsgnSAD = analyze( existsAsgn, vars )

    assertEqualSAD( existsAsgnSAD,
      StaticAnalysisData(
        Set( asgn.ID.id ),
        Set( (asgn.ID.id, asgn.ID.id) ),
        Set.empty,
        Map( "x" -> Variable( asgn.ID.id ), "y" -> False() ),
        Map( asgn.ID.id -> Set("y") ),
        Map( asgn.ID.id -> asgn )
      )
    )

    assert( existsAsgnSAD.simplified.delta == existsAsgnSAD.delta )

    val existsDoubleAsgnSAD = analyze( existsDoubleAsgn, vars )

    assertEqualSAD( existsDoubleAsgnSAD, existsAsgnSAD )

    val existsCmpSAD = analyze( existsCmp, vars )

    assertEqualSAD( existsCmpSAD, defaultEmptySAD )

    val existsDoubleCmpSAD = analyze( existsDoubleCmp, vars )

    assertEqualSAD( existsDoubleCmpSAD, existsCmpSAD )
  }

  test( "Test staticAnalysis: ITE" ){
    val asgnX1 = primeEq( n_x, int( 1 ) )
    val asgnX2 = primeEq( n_x, int( 2 ) )
    val cmpX1 = eql( n_x, int( 1 ) )
    val cmpX2 = eql( n_x, int( 2 ) )

    val balancedITE = ite( falseEx, asgnX1, asgnX2 )
    val imbalancedITE = ite( falseEx, asgnX1, cmpX1 )
    val conditionITE = ite( falseEx, cmpX1, cmpX2 )

    val balancedITESAD = analyze( balancedITE, vars )

    assertEqualSAD( balancedITESAD,
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
      balancedITESAD.simplified.delta ==
        Map( "x" -> And( Variable( asgnX1.ID.id ), Variable( asgnX2.ID.id ) ), "y" -> False() )
    )

    val imbalancedITESAD = analyze( imbalancedITE, vars )

    assertEqualSAD( imbalancedITESAD,
      StaticAnalysisData(
        Set( asgnX1.ID.id ),
        Set( (asgnX1.ID.id, asgnX1.ID.id) ),
        Set.empty,
        Map( "x" -> And( Variable( asgnX1.ID.id ), False() ), "y" -> And( False(), False() ) ),
        Map( asgnX1.ID.id -> Set.empty[String] ),
        Map( asgnX1.ID.id -> asgnX1 )
      )
    )
    assert( imbalancedITESAD.simplified.delta == defaultVarsDelta )

    val conditionITESAD = analyze( conditionITE, vars )

    assertEqualSAD( conditionITESAD,
      defaultEmptySAD.copy(
        delta = Map( "x" -> And( False(), False() ), "y" -> And( False(), False() ) )
      )
    )
    assert( conditionITESAD.simplified.delta == defaultVarsDelta )

  }

  test( "Test staticAnalysis: LET-IN" ){
    val asgnX = primeEq( n_x, int( 1 ) )
    val asgnY1 = primeEq( n_y, int( 1 ) )
    val asgnY2 = primeEq( n_y, int( 2 ) )
    val xDecl = declOp( "X", asgnX )
    val bodySingle = appDecl( xDecl )
    val bodyOr =
      or(
        and( appDecl( xDecl ), asgnY1 ),
        and( appDecl( xDecl ), asgnY2 )
      )

    val letInSingle = letIn( bodySingle, xDecl )
    val letInOr = letIn( bodyOr, xDecl )

    val asgnSAD = analyze( asgnX, vars )

    val letInSingleSAD = analyze( letInSingle, vars )

    assertEqualSAD( letInSingleSAD, asgnSAD )

    val letInOrSAD = analyze( letInOr, vars )

    assertEqualSAD( letInOrSAD,
      StaticAnalysisData(
        Set( asgnX.ID.id, asgnY1.ID.id, asgnY2.ID.id ),
        Set(
          (asgnX.ID.id, asgnX.ID.id), (asgnY1.ID.id, asgnY1.ID.id), (asgnY2.ID.id, asgnY2.ID.id),
          (asgnX.ID.id, asgnY1.ID.id), (asgnY1.ID.id, asgnX.ID.id),
          (asgnX.ID.id, asgnY2.ID.id), (asgnY2.ID.id, asgnX.ID.id)
        ),
        Set( (asgnY1.ID.id, asgnY2.ID.id), (asgnY2.ID.id, asgnY1.ID.id) ),
        Map(
          "x" ->
            And(
              Or( Variable( asgnX.ID.id ), False() ),
              Or( Variable( asgnX.ID.id ), False() )
            ),
          "y" ->
            And(
              Or( False(), Variable( asgnY1.ID.id ) ),
              Or( False(), Variable( asgnY2.ID.id ) )
            )
        ),
        Map( asgnX.ID.id -> Set.empty[String], asgnY1.ID.id -> Set.empty[String], asgnY2.ID.id -> Set.empty[String] ),
        Map( asgnX.ID.id -> asgnX, asgnY1.ID.id -> asgnY1, asgnY2.ID.id -> asgnY2 )
      )
    )

    assert( letInOrSAD.simplified.delta ==
      Map(
        "x" -> And( Variable( asgnX.ID.id ), Variable( asgnX.ID.id ) ),
        "y" -> And( Variable( asgnY1.ID.id ), Variable( asgnY2.ID.id ) )
      )
    )

  }

}
