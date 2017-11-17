package at.forsyte.apalache.tla.lir


import at.forsyte.apalache.tla.lir.oper.{FixedArity, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.plugins.Identifier
import at.forsyte.apalache.tla.lir.{Builder => bd}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner


@RunWith( classOf[JUnitRunner] )
class TestOperatorHandler extends FunSuite {
  val testFolderPath = "src/test/resources/"
  val bodyDB         = new BodyDB()
  val sourceDB       = new SourceDB()


  test( "Test bodyDB" ) {
  }


  test( "Test simple substitutions" ) {
    bodyDB.clear()
    sourceDB.clear()

    val ex = bd.appOp( bd.name( "f" ), bd.cup( bd.name( "i" ), bd.name( "j" ) ) )
    val newEx1 = OperatorHandler.replaceAll( ex, bd.name( "i" ), bd.int( 0 ) )
    val newEx2 = OperatorHandler.replaceAll( ex, bd.name( "k" ), bd.int( 0 ) )

    assert( newEx1 == bd.appOp( bd.name( "f" ), bd.cup( bd.int( 0 ), bd.name( "j" ) ) ) )
    assert( newEx2 == ex )
  }

  test( "Test higher-order operators" ) {
    bodyDB.clear()
    sourceDB.clear()

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
    val op_B = TlaOperDecl( "B", List( SimpleFormalParam( "z" ) ), bd.name( "z" ) )

    val op_C = TlaOperDecl( "C", List(),
      OperEx( op_A.operator, bd.int( 0 ), bd.int( 1 ), bd.name( "B" ) )
    )

    val spec = TlaSpec( "level2Operators", List( op_A, op_B, op_C ) )

    OperatorHandler.extract( spec, bodyDB )

    val unfolded1 = OperatorHandler.unfoldOnce( op_C.body, bodyDB )
    val unfolded2 = OperatorHandler.unfoldOnce( unfolded1, bodyDB )
    val unfolded3 = OperatorHandler.unfoldOnce( unfolded2, bodyDB )

    assert( unfolded1 == bd.appOp( bd.name( "B" ), bd.cup( bd.int( 0 ), bd.int( 1 ) ) ) )
    assert( unfolded2 == bd.cup( bd.int( 0 ), bd.int( 1 ) ) )
    assert( unfolded3 == unfolded2 )

    val maxUnfold = OperatorHandler.unfoldMax( op_C.body, bodyDB )

    assert( maxUnfold == unfolded2 )

    val noUnfold = OperatorHandler.unfoldOnce( op_C.body, new BodyDB() )

    assert( noUnfold == op_C.body )

  }

  test( "Test higher-order operators with nesting" ) {
    bodyDB.clear()
    sourceDB.clear()
    //      """
    //        |---- MODULE level2Operators ----
    //        |A(arg, Op(_)) == Op(arg)
    //        |B(z) == z
    //        |C == A(A(B(0),B),B)
    //        |================================
    //      """
    val op_A =
      TlaOperDecl(
        "A",
        List(
          SimpleFormalParam( "arg" ),
          OperFormalParam( "Op", FixedArity( 1 ) )
        ),
        bd.appOp( bd.name( "Op" ), bd.name( "arg" ) )
      )
    val op_B = TlaOperDecl( "B", List( SimpleFormalParam( "z" ) ), bd.name( "z" ) )

    val op_C = TlaOperDecl( "C", List(),
      OperEx(
        op_A.operator,
        OperEx(
          op_A.operator,
          OperEx(
            op_B.operator,
            bd.int( 0 )
          ),
          bd.name( "B" )
        ),
        bd.name( "B" ) )
    )

    val spec = TlaSpec( "insaneNesting", List( op_A, op_B, op_C ) )

    OperatorHandler.extract( spec, bodyDB )

    val unfolded = OperatorHandler.unfoldMax( op_C.body, bodyDB )

    assert( unfolded == bd.int( 0 ) )
  }

  test( "Test SourceDB" ){
    bodyDB.clear()
    sourceDB.clear()

    val ex = bd.appOp( bd.name( "f" ), bd.cup( bd.name( "i" ), bd.name( "j" ) ) )

    Identifier.identify(ex)

    val newEx1 = OperatorHandler.replaceAll( ex, bd.name( "i" ), bd.int( 0 ), sourceDB )

    val original1 = OperatorHandler.undoReplace( newEx1 ,sourceDB )
    val cup = ex.asInstanceOf[OperEx].args.tail.head
    val newCup = newEx1.asInstanceOf[OperEx].args.tail.head
    val original2 = OperatorHandler.undoReplace( newCup ,sourceDB )


    assert( original1 identical ex )
    assert( original2 identical cup )


  }
}