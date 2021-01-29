package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestSmtFreeSTE extends FunSuite with TestingPredefs {

  val sourceLoc = new SourceLocator( Map.empty, new ChangeListener )

  val ste = new SmtFreeSymbolicTransitionExtractor( TrackerWithListeners(), sourceLoc )

  test( "Single ex: candidate" ) {
    val ex = tla.primeEq( n_x, 1 )
    val vars = Set( "x" )
    val strat = ste.getStrategy( vars, ex )

    assert( strat == Seq( ex.ID ) )
  }

  test( "Single ex: manual asgn" ) {
    val ex = tla.assignPrime( n_x, 1 )
    val vars = Set( "x" )
    val strat = ste.getStrategy( vars, ex )

    assert( strat == Seq( ex.ID ) )
  }

  test( "2 candidates: Manual / natural" ) {
    val manual = tla.assignPrime( n_x, 1 )
    val natural = tla.primeEq( n_x, 1 )
    val vars = Set( "x" )

    val ex1 = tla.and( manual, natural )
    val strat1 = ste.getStrategy( vars, ex1 )

    assert( strat1 == Seq( manual.ID ) )

    val ex2 = tla.and( natural, manual )
    assertThrows[AssignmentException] {
      ste.getStrategy( vars, ex2 )
    }

  }

  test( "Missing var" ) {
    val ex = tla.primeEq( n_x, 1 )
    val vars = Set( "x", "y" )

    assertThrows[AssignmentException] {
      ste.getStrategy( vars, ex )
    }
  }

  test( "Assignment in LET-IN" ) {
    val asgn = tla.primeEq( n_x, 1 )
    val declA = tla.declOp( "A", asgn )
    val ex = tla.letIn( tla.appDecl( declA ), declA )

    val vars = Set( "x" )

    val strat = ste.getStrategy( vars, ex )

    val x = 1
    assert( x == 1 && strat == Seq( asgn.ID ) )
  }

  test( "Disjunction" ) {
    val asgn1 = tla.primeEq( n_x, 1 )
    val asgn2 = tla.primeEq( n_x, 2 )
    val ex = tla.or( asgn1, asgn2 )
    val vars = Set( "x" )
    val strat = ste.getStrategy( vars, ex )

    assert( strat == Seq( asgn1.ID, asgn2.ID ) )
  }

  test( "Use before assignment" ) {
    val asgn = tla.primeEq( n_x, 1 )
    val cmp = tla.gt( tla.prime( n_x ), 0 )
    val ex = tla.and( cmp, asgn )
    val vars = Set( "x" )

    assertThrows[AssignmentException] {
      ste.getStrategy( vars, ex )
    }
  }


}
