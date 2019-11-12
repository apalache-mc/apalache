package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestTypeReduction extends FunSuite with BeforeAndAfter {

  var gen = new SmtVarGenerator
  var tr  = new TypeReduction( gen )

  before {
    gen = new SmtVarGenerator
    tr = new TypeReduction( gen )
  }

  test( "Test nesting" ) {
    val tau = FunT( IntT, SetT( IntT ) )
    val m = Map.empty[TypeVar, SmtTypeVariable]
    val rr = tr.reduce( tau, m )
    assert( rr.t == fun( int, set( int ) ) )
  }

  test("Test tuples"){
    val tau = SetT( FunT( TupT( IntT, StrT ), SetT( IntT ) ) )
    val m = Map.empty[TypeVar, SmtTypeVariable]
    val rr = tr.reduce(tau, m)
    val idx = SmtIntVariable( 0 )
    assert( rr.t == set( fun( tup( idx ), set( int ) ) ) )
    assert( rr.phi.contains( hasIndex( idx, 0, int ) ) )
    assert( rr.phi.contains( hasIndex( idx, 1, str ) ) )
  }

  test( "Test seq" ){
    val tau = RecT( Map( "a" -> SeqT( IntT ) ) )
    val m = Map.empty[TypeVar, SmtTypeVariable]
    val rr = tr.reduce(tau, m)
    val idx = SmtIntVariable( 0 )
    assert( rr.t == rec( idx ) )
    assert( rr.phi.contains( hasField( idx, "a", seq( int ) ) ) )
  }

  test( "Test poly/sparseTup" ){
    val tau = PolyOperT( List.empty, OperT( TupT( IntT ), SparseTupT( Map( 3 -> IntT ) ) ) )
    val m = Map.empty[TypeVar, SmtTypeVariable]
    val rr = tr.reduce(tau, m)

    val assertCond = rr.t match {
      case oper( _, tup( j ) ) =>
        rr.phi.contains( hasIndex( j, 3, int ) )
      case _ => false
    }

    assert( assertCond )
  }
}
