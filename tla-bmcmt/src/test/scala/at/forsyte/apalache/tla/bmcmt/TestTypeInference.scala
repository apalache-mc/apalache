package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{Signatures, TypeInference}
import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.plugins.Identifier
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestTypeInference extends FunSuite with TestingPredefs {

  ignore( "Signatures" ) {
    val exs = List(
      tla.and( n_x, n_y ),
      tla.choose( n_x, n_S, n_p ),
      tla.enumSet( seq( 10 ) : _* ),
      tla.in( n_x, n_S ),
      tla.map( n_e, n_x, n_S)
    )

    exs foreach Identifier.identify

    val sigs = exs map Signatures.get

    exs zip sigs foreach {case (x,y) => println(s"${x}  ...  ${y}") }

  }

  test( "TypeInference" ) {
    val ex = tla.and( tla.primeEq( n_a ,  tla.choose( n_x, n_S, n_p )), tla.in( 2, n_S ) )

    Identifier.identify( ex )

    val r = TypeInference.theta( ex )

    println( r )

  }
}
