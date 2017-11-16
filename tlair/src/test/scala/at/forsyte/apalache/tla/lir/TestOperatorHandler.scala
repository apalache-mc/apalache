package at.forsyte.apalache.tla.lir



import at.forsyte.apalache.tla.lir.oper.{FixedArity, TlaOper, TlaSetOper}

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner


@RunWith( classOf[JUnitRunner] )
class TestOperatorHandler extends FunSuite {
  val testFolderPath = "src/test/resources/"
  val bd = Builder

  ignore( "Test simple substitutions" ){
    val ex = bd.appOp( bd.name( "f" ), bd.cup( bd.name( "i" ), bd.name( "j" ) ) )
    val newEx = OperatorHandler.replaceAll( ex, bd.name( "i" ), bd.int( 0 ) )

    println(ex)
    println(newEx)

  }

  test( "Test higher-order operators" ) {
    //      """
    //        |---- MODULE level2Operators ----
    //        |VARIABLE x, y
    //        |A(i, j, f(_)) == f(i \cup j)
    //        |B(z) == z
    //        |C == A(0, 1, B)
    //        |================================
    //      """
    val op_A =
      TlaOperDecl(
        "A",
        List(
          SimpleFormalParam( "i" ),
          SimpleFormalParam( "j" ),
          OperFormalParam( "f", FixedArity( 2 ) )
        ),
        bd.appOp( bd.name( "f" ), bd.cup( bd.name( "i" ), bd.name( "j" ) ) )
      )
    val op_B = TlaOperDecl( "B", List( SimpleFormalParam( "z" ) ), bd.name("z") )

    val op_C = TlaOperDecl( "C", List(),
      OperEx( op_A.operator, bd.int(0), bd.int(1), bd.name("B") )
    )

    val spec = TlaSpec( "level2Operators", List( op_A, op_B, op_C ) )

    OperatorHandler.extract( spec )

    OperatorHandler.implBodyDB.print

    val unfolded1 = OperatorHandler.unfoldOnce( op_C.body )
    val unfolded2 = OperatorHandler.unfoldOnce( unfolded1 )
    val unfolded3 = OperatorHandler.unfoldOnce( unfolded2 )
    val unfolded4 = OperatorHandler.unfoldOnce( unfolded3 )

    println( op_C.body )
    println( unfolded1 )
    println( unfolded2 )
    println( unfolded3 )
    println( unfolded4 )

    val maxUnfold = OperatorHandler.unfoldMax( op_C.body )

    println( maxUnfold )

  }
}