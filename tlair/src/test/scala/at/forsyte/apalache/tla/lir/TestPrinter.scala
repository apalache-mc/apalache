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
  val bd = Builder

  val up = UTFPrinter
  val sp = SimplePrinter

  object rmp extends Printer {
    def apply( p_ex: TlaEx ) : String = UTFPrinter.apply( p_ex, true )
  }

  val n_a = NameEx( "a" )
  val n_b = NameEx( "b" )
  val n_c = NameEx( "c" )
  val n_d = NameEx( "d" )
  val n_e = NameEx( "e" )

  test( "Test UTF8" ) {

    val ex = bd.forall( bd.name( "p" ), bd.name( "S" ), bd.le( bd.name( "p" ), bd.name( "q" ) ) )
    val ret = up( ex )

    val ex2 = bd.mod( n_a, n_b )

    println( ret )
    println( up( ex2 ) )
    println( up( bd.comp( n_a, n_b ) ) )

    val caseEx1 = bd.caseAny( n_a, n_a, n_a, n_a, n_a, n_a )
    val caseEx2 = bd.caseAny( n_a, n_a, n_a, n_a, n_a )

    println( up( caseEx1 ) )
    println( up( caseEx2 ) )

    val AAEx1 = bd.AA( n_a, n_b )

    println( up( AAEx1 ) )

    val SFEx1 = bd.SF( n_a, n_b )

    println( up( SFEx1 ) )

    val appEx1 = bd.appOp( n_a )
    val appEx2 = bd.appOp( n_a, n_b )

    println( up( appEx1 ) )
    println( up( appEx2 ) )

    val enumFnEx1 = bd.enumFun( n_a, n_b, n_a, n_b, n_c, n_d )

    println( up( enumFnEx1 ) )

    val exceptEx1 = bd.except( n_a, n_b, n_c, n_d, n_e )

    println( up( exceptEx1 ) )

    val fnDefEx1 = bd.funDef( n_a, n_b, n_c, n_d, n_e )

    println( up( fnDefEx1 ) )

    val tplEx1 = bd.tuple( n_a, n_b, n_c )

    println( up( tplEx1 ) )

    val mapEx1 = bd.map( n_a, n_b, n_c, n_d, n_e )

    println( up( mapEx1 ) )

    val timesEx1 = bd.times( n_a, n_b, n_c, n_d )
    val timesEx2 = bd.times( n_a )
    val timesEx3 = bd.times()

    println( up( timesEx1 ) )
    println( up( timesEx2 ) )
    println( up( timesEx3 ) )


  }

}
