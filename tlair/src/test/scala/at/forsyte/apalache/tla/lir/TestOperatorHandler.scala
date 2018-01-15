package at.forsyte.apalache.tla.lir


import at.forsyte.apalache.tla.lir.oper.FixedArity
import at.forsyte.apalache.tla.lir.plugins.{Identifier, UniqueDB}
import at.forsyte.apalache.tla.lir.{Builder => bd, OperatorHandler => oh}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner


@RunWith( classOf[JUnitRunner] )
class TestOperatorHandler extends FunSuite with TestingPredefs {
  val testFolderPath = "src/test/resources/"
  val bodyDB         = new BodyDB()
  val sourceDB       = new SourceDB()


  test( "Test extract" ) {
    bodyDB.clear()

    val declEx1 = TlaVarDecl( "x" )
    val declEx2 = TlaOperDecl( "A2", List(), 42 )
    val declEx3 = TlaOperDecl( "B2", List( "x", ("y", 2) ), bd.exp( bd.appOp( "y", "x", "x" ), 2 ) )

    oh.extract( declEx1, bodyDB )
    assert( bodyDB.size() == 0 )

    oh.extract( declEx2, bodyDB )
    assert( bodyDB.size() == 1 && bodyDB.contains( "A2" ) )

  }


  test( "Test simple substitutions" ) {
    bodyDB.clear()
    sourceDB.clear()

    val ex = bd.appOp( bd.name( "f" ), bd.cup( bd.name( "i" ), bd.name( "j" ) ) )
    val newEx1 = OperatorHandler.replaceAll( ex, bd.name( "i" ), bd.bigInt( 0 ) )
    val newEx2 = OperatorHandler.replaceAll( ex, bd.name( "k" ), bd.bigInt( 0 ) )

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
          OperFormalParam( "f", FixedArity( 2 ) )
        ),
        bd.appOp( bd.name( "f" ), bd.cup( bd.name( "i" ), bd.name( "j" ) ) )
      )
    val op_B = TlaOperDecl( "B", List( SimpleFormalParam( "z" ) ), bd.name( "z" ) )

    val op_C = TlaOperDecl( "C", List(),
      OperEx( op_A.operator, bd.bigInt( 0 ), bd.bigInt( 1 ), bd.name( "B" ) )
    )

    val spec = TlaSpec( "level2Operators", List( op_A, op_B, op_C ) )

    OperatorHandler.extract( spec, bodyDB )

    val unfolded1 = OperatorHandler.unfoldOnce( op_C.body, bodyDB )
    val unfolded2 = OperatorHandler.unfoldOnce( unfolded1, bodyDB )
    val unfolded3 = OperatorHandler.unfoldOnce( unfolded2, bodyDB )

    assert( unfolded1 == bd.appOp( bd.name( "B" ), bd.cup( bd.bigInt( 0 ), bd.bigInt( 1 ) ) ) )
    assert( unfolded2 == bd.cup( bd.bigInt( 0 ), bd.bigInt( 1 ) ) )
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
            bd.bigInt( 0 )
          ),
          bd.name( "B" )
        ),
        bd.name( "B" ) )
    )

    val spec = TlaSpec( "insaneNesting", List( op_A, op_B, op_C ) )

    OperatorHandler.extract( spec, bodyDB )

    val unfolded = OperatorHandler.unfoldMax( op_C.body, bodyDB )

    assert( unfolded == bd.bigInt( 0 ) )
  }

  test( "Test SourceDB" ) {
    bodyDB.clear()
    sourceDB.clear()

    val ex = bd.appOp( bd.name( "f" ), bd.cup( bd.name( "i" ), bd.name( "j" ) ) )

    Identifier.identify( ex )

    val newEx1 = OperatorHandler.replaceAll( ex, bd.name( "i" ), bd.bigInt( 0 ), sourceDB )

    val original1 = OperatorHandler.undoReplace( newEx1, sourceDB )
    val cup = ex.asInstanceOf[OperEx].args.tail.head
    val newCup = newEx1.asInstanceOf[OperEx].args.tail.head
    val original2 = OperatorHandler.undoReplace( newCup, sourceDB )


    assert( original1 identical ex )
    assert( original2 identical cup )


  }

  test( "Test SourceDB with uniqueVarRename" ){
    UniqueDB.clear()

    val sdb = new SourceDB()

    val bodyA = bd.exists( n_x, n_S, bd.exists( n_y, n_T, bd.eql( bd.plus( n_x, n_y ), bd.plus( n_a, n_b ) ) ) )
    val opA = bd.declOp( "A", bodyA, "a", "b")
    Identifier.identify( opA )

    val newA = OperatorHandler.uniqueVarRename( Seq(opA), sdb ).head.asInstanceOf[TlaOperDecl]
    val newBodyA = newA.body

    assert( newBodyA.valid )

    val originalHopefully = UniqueDB apply sdb.traceBack( newBodyA.ID )


    def leafJudge( p_ex : TlaEx) : Boolean = {
      p_ex match {
        case ex : OperEx => false
        case _ => true
      }
    }

    def leafFun( p_ex : TlaEx ) : Boolean = {
      p_ex match {
        case NameEx( name ) if name.startsWith( "A_" ) => {
          val anc = sdb.traceBack( p_ex.ID )
          UniqueDB.contains( anc ) && UniqueDB.get(anc) == NameEx( name.substring( 2 ) )
        }
        case _ => true
      }
    }

    def parentFun( p_ex : TlaEx, p_childVals : Seq[Boolean] ) : Boolean = {
      val allChildren = p_childVals.forall( x => x )
      allChildren
    }
    def default = true

    val allOK = SpecHandler.bottomUpVal[Boolean]( newBodyA, leafJudge, leafFun, parentFun, default )

    assert( allOK )

  }
}