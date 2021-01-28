package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.TestingPredefs
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestTypeReduction extends FunSuite with TestingPredefs with BeforeAndAfter {

  var gen = new SmtVarGenerator
  var tr  = new TypeReduction( gen )

  before {
    gen = new SmtVarGenerator
    tr = new TypeReduction( gen )
  }

  test( "Test nesting" ) {
    val tau = FunT( IntT, SetT( IntT ) )
    val m = Map.empty[TypeVar, SmtTypeVariable]
    val rr = tr( tau, m )
    assert( rr.t == fun( int, set( int ) ) )
  }

  test("Test tuples"){
    val tau = SetT( FunT( TupT( IntT, StrT ), SetT( IntT ) ) )
    val m = Map.empty[TypeVar, SmtTypeVariable]
    val rr = tr(tau, m)
    val idx = SmtIntVariable( 0 )
    assert( rr.t == set( fun( tup( idx ), set( int ) ) ) )
    assert( rr.phi.contains( hasIndex( idx, 0, int ) ) )
    assert( rr.phi.contains( hasIndex( idx, 1, str ) ) )
  }
}
