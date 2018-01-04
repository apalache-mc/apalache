package at.forsyte.apalache.tla.lir

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.{Builder => bd}

import at.forsyte.apalache.tla.lir.stdfun._

@RunWith( classOf[JUnitRunner] )
class TestStdFun extends FunSuite with TestingPredefs {
  test( "filter Null" ) {

    def filterFun( p_ex : TlaEx ) : Boolean = !p_ex.isNull

    val ex1 = bd.plus( 2, bd.enumSet( NullEx, NullEx ) )
    val ex2 = bd.plus( 2, bd.plus( NullEx, NullEx ) )

    val filtered1 = filter( ex1, filterFun )

    assert( filtered1 == bd.plus( 2, bd.enumSet() ) )
    assertThrows[FilterInvalidationError]( filter( ex2, filterFun ) )
    try {
      filter( ex2, filterFun )
    }
    catch {
      case e : FilterInvalidationError => println( e )
      case _ =>
    }


  }
}
