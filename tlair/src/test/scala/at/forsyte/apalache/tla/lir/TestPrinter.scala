package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.{LetInOper, TlaControlOper}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.temporal.TlaTempOper
import at.forsyte.apalache.tla.lir.values._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestPrinter extends FunSuite {
  test( "Test UTF8" ) {
    val ex = Builder.forall( Builder.name( "p" ), Builder.le( Builder.name( "p" ), Builder.name( "q" ) ) )

    val ret = SimplePrinter( ex )

    println( ret )

  }

}
