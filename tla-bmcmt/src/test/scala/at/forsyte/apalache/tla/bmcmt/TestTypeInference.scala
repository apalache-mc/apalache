package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{Signatures, TypeInference}
import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.lir.convenience._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

// TODO: remove?
@RunWith( classOf[JUnitRunner] )
class TestTypeInference extends FunSuite with TestingPredefs {

  ignore( "Signatures" ) {
    val exs = List(
      tla.and( n_x, n_y ),
      tla.choose( n_x, n_S, n_p ),
      tla.enumSet( seq( 10 ) : _* ),
      tla.in( n_x, n_S ),
      tla.map( n_e, n_x, n_S )
    )

    val sigs = exs map Signatures.get

    exs zip sigs foreach { case (x, y) => println( s"${x}  ...  ${y}" ) }

    val funDef = tla.funDef( tla.plus( n_x, n_y ), n_x, n_S, n_y, n_T )

    val sig = Signatures.get( funDef )

    printsep()
    println( sig )
    printsep()
  }

  ignore( "TypeInference" ) {
    val ex = tla.and( tla.primeEq( n_a, tla.choose( n_x, n_S, n_p ) ), tla.in( 2, n_S ) )

    val r = TypeInference.theta( ex )

    println( r )

  }

  ignore( "Application" ) {

    val ex = tla.eql( tla.plus(  tla.appFun( n_f, n_x ) , 2), 4 )
    val ex2 =
      tla.and(
        tla.in( n_x, n_S ),
        tla.le(
          tla.plus(
            tla.mult( 2, n_x ),
            5
          ),
          10
        ),
        tla.primeEq( n_x,
          tla.appFun(
            n_f,
            n_x
          )
        )
      )

    val r = TypeInference( ex )
  }
}
