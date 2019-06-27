package at.forsyte.apalache.tla.lir


import at.forsyte.apalache.tla.lir.db.{BodyDB, SourceStoreImpl}
import at.forsyte.apalache.tla.lir.oper.FixedArity
import at.forsyte.apalache.tla.lir.{Builder => bd, OperatorHandler => oh}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner


@RunWith( classOf[JUnitRunner] )
class TestOperatorHandler extends FunSuite with TestingPredefs {
  val testFolderPath = "src/test/resources/"
  val bodyDB         = new BodyDB()
  val sourceDB       = new SourceStoreImpl()


  test( "Test extract" ) {
    bodyDB.clear()

    val declEx1 = TlaVarDecl( "x" )
    val declEx2 = TlaOperDecl( "A2", List(), 42 )
    val declEx3 = TlaOperDecl( "B2", List( "x", ("y", 2) ), bd.exp( bd.appOp( "y", "x", "x" ), 2 ) )

    oh.extract( declEx1, bodyDB )
    assert( bodyDB.size == 0 )

    oh.extract( declEx2, bodyDB )
    assert( bodyDB.size == 1 && bodyDB.contains( "A2" ) )

  }


  test( "Test simple substitutions" ) {
    bodyDB.clear()
    sourceDB.clear()

    val ex = bd.appOp( bd.name( "f" ), bd.cup( bd.name( "i" ), bd.name( "j" ) ) )
    val newEx1 = OperatorHandler.replaceAll( ex, bd.name( "i" ), bd.bigInt( 0 ), new SourceStoreImpl )
    val newEx2 = OperatorHandler.replaceAll( ex, bd.name( "k" ), bd.bigInt( 0 ), new SourceStoreImpl )

    assert( newEx1 == bd.appOp( bd.name( "f" ), bd.cup( bd.bigInt( 0 ), bd.name( "j" ) ) ) )
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
          OperFormalParam( "f", FixedArity( 1 ) )
        ),
        bd.appOp( bd.name( "f" ), bd.cup( bd.name( "i" ), bd.name( "j" ) ) )
      )
    val op_B = TlaOperDecl( "B", List( SimpleFormalParam( "z" ) ), bd.name( "z" ) )

    val op_C = TlaOperDecl( "C", List(),
      OperEx( op_A.operator, bd.bigInt( 0 ), bd.bigInt( 1 ), bd.name( "B" ) )
    )

    val spec = TlaSpec( "level2Operators", List( op_A, op_B, op_C ) )

    OperatorHandler.extract( spec, bodyDB )

    val ssi = new SourceStoreImpl

    val unfolded1 = OperatorHandler.unfoldOnce( op_C.body, bodyDB, ssi )
    val unfolded2 = OperatorHandler.unfoldOnce( unfolded1, bodyDB, ssi )
    val unfolded3 = OperatorHandler.unfoldOnce( unfolded2, bodyDB, ssi )

    assert( unfolded1 == bd.appOp( bd.name( "B" ), bd.cup( bd.bigInt( 0 ), bd.bigInt( 1 ) ) ) )
    assert( unfolded2 == bd.cup( bd.bigInt( 0 ), bd.bigInt( 1 ) ) )
    assert( unfolded3 == unfolded2 )

    val maxUnfold = OperatorHandler.unfoldMax( op_C.body, bodyDB, sourceDB )

    assert( maxUnfold == unfolded2 )

    val noUnfold = OperatorHandler.unfoldOnce( op_C.body, new BodyDB(), new SourceStoreImpl )

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
            bd.bigInt( 0 )
          ),
          bd.name( "B" )
        ),
        bd.name( "B" ) )
    )

    val spec = TlaSpec( "insaneNesting", List( op_A, op_B, op_C ) )

    OperatorHandler.extract( spec, bodyDB )

    val unfolded = OperatorHandler.unfoldMax( op_C.body, bodyDB, sourceDB )

    assert( unfolded == bd.bigInt( 0 ) )
  }
}