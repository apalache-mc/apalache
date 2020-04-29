package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.types.TypeComputer.IncompatibleTypesException
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestTypeComputer extends FunSuite with TestingPredefs with BeforeAndAfter {

  import Builder._

  ignore( "1" ) {
    val bm = BodyMapFactory.newMap
    val binding = Map( "x" -> TypeVar( 99 ) )

    val tc = new TypeComputer( bm, binding )

    val ex = plus( n_x, int( 1 ) )
    val sub = tc.buildTypeAssignment( Map.empty, ex ).substitution
    val (_, bnd, _) = tc.getWithSubsitution( sub )
    assert( bnd( "x" ) == IntT )
  }

  ignore( "2" ) {
    val bm = BodyMapFactory.newMap
    val binding = Map( "x" -> TypeVar( 99 ) )

    val tc = new TypeComputer( bm, binding )

    val ex = or(
      eql( n_x, int( 1 ) ),
      eql( n_x, str( "1" ) )
    )
    assertThrows[IncompatibleTypesException] {
      tc.buildTypeAssignment( Map.empty, ex )
    }
  }

  ignore( "3" ) {
    val aDecl = declOp( "A", n_p, "p" )
    val bDecl = declOp( "B", appDecl( aDecl, int( 1 ) ) )

    val bm = BodyMapFactory.makeFromDecls( Seq( aDecl, bDecl ) )
    val binding = Map( "p" -> TypeVar( 99 ) )

    val tc = new TypeComputer( bm, binding )

    val ex = appDecl( bDecl )

    val sub = tc.buildTypeAssignment( Map.empty, ex ).substitution
    val ret@(asgn, _,_) = tc.getWithSubsitution( sub )
    assert( asgn( ex.ID ) == IntT )

  }

  ignore( "4" ) {
    val aDecl = declOp( "A", n_p, "p" )
    val appAInt = appDecl( aDecl, int( 1 ) )
    val appAStr = appDecl( aDecl, str( "1" ) )
    val bDecl = declOp( "B",
      and(
        eql( appAInt, int( 1 ) ),
        eql( appAStr, str( "1" ) )
      )
    )

    val bm = BodyMapFactory.makeFromDecls( Seq( aDecl, bDecl ) )
    val binding = Map( "p" -> TypeVar( 99 ) )

    val tc = new TypeComputer( bm, binding )

    val ex = appDecl( bDecl )

    val sub = tc.buildTypeAssignment( Map.empty, ex ).substitution
    val ret@(asgn, _,_) = tc.getWithSubsitution( sub )
    assert( asgn( appAInt.ID ) == IntT )
    assert( asgn( appAStr.ID ) == StrT )
  }

  test("5"){

    val aDecl = declOp( "A",
      tuple( n_p, str( "c" ), n_x, plus( n_q, int( 1 ) ) ),
      "p", "q" )
    val backMap = aux.uidToExMap( aDecl.body )

    val bm = BodyMapFactory.makeFromDecl( aDecl )
    val binding = Map(
      "x" -> TypeVar(99),
      "p" -> TypeVar(100),
      "q" -> TypeVar(101)
    )
    val tc = new TypeComputer( bm, binding )

    val ex = aDecl.body

    val sub = tc.buildTypeAssignment( Map.empty, ex ).substitution
    val ret@(_,_,operTs) = tc.getWithSubsitution( sub )
    assert( operTs( aDecl.name ) ==
      OperT( TupT( binding( "p" ), IntT ), TupT( binding( "p" ), StrT, binding( "x" ), IntT ) )
    )

    
  }

}
