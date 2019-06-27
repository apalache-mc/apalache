package at.forsyte.apalache.tla.lir


import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner


@RunWith( classOf[JUnitRunner] )
class TestEnvHandler extends FunSuite with TestingPredefs {

  def newEh : EnvironmentHandler = EnvironmentHandlerGenerator.makeEH

  test( "VarRename" ) {
    val eh = EnvironmentHandlerGenerator.makeEH

    val paramName = "a"
    val operName = "MyOper"

    val letInOperName = "A"
    val letInParamName = "b"

    val aOper = tla.declOp( letInOperName, letInParamName, letInParamName )

    val ex = tla.letIn(
      tla.exists( n_x, n_S, tla.eql( tla.plus( n_x, paramName ), tla.appOp( letInOperName, paramName ) ) ),
      aOper )

    eh.identify( ex )

    val decl = tla.declOp( operName, ex, paramName )

    val newDecls = eh.uniqueVarRename( Seq( decl ) )

    assert( newDecls.size === 1 )

    val newDecl = newDecls.head

    assert( newDecl.isInstanceOf[TlaOperDecl] )

    val castNewDecl = newDecl.asInstanceOf[TlaOperDecl]

    assert( decl.name === newDecl.name )
    assert( decl.formalParams.map( eh.AuxFun.renameParam( operName ) ) === castNewDecl.formalParams )
    assert( decl.body !== castNewDecl.body )

  }

  test( "Extract" ) {
    val ehReal = EnvironmentHandlerGenerator.makeEH
    val ehDummy = EnvironmentHandlerGenerator.makeDummyEH

    val decl = tla.declOp( "X", 1 )

    ehReal.extract( decl )
    ehDummy.extract( decl )

    assert( ehReal.m_bodyDB.size === 1 )
    assert( ehDummy.m_bodyDB.size === 0 )

  }

  test( "Unfold 1x" ) {
    val eh = newEh

    val opName1 = "X"
    val opName2 = "Y"
    val opName3 = "Z"

    val paramName1 = "a"
    val paramName2 = "b"

    val decl1 = tla.declOp( opName1, 1 )
    val decl2 = tla.declOp( opName2, tla.plus( paramName1, 2 ), paramName1 )
    val decl3 = tla.declOp( opName3, tla.eql( paramName1, paramName2 ), paramName1, paramName2 )


    eh.extract( decl1 )
    eh.extract( decl2 )
    eh.extract( decl3 )

    eh.m_bodyDB.print()

    val appEx =  tla.appOp( opName2, 3 )
    val uo = new TlaUserOper( opName3, decl3.formalParams.size, decl3 )
    val uopEx = OperEx( uo, 42, 103 )

    val ex1 = tla.plus( opName1, 2 )
    val ex2 = tla.and( trueEx, appEx )
    val ex3 = tla.exists( n_x, n_S,  uopEx )
    val ex4 = tla.appOp( opName2, tla.appOp(opName2, 1 ) )

//    println( ex4 )

    //    eh.m_bodyDB.print( )


    val unfolded1 = eh.unfoldOnce( ex1 )
    val unfolded2 = eh.unfoldOnce( ex2 )
    val unfolded3 = eh.unfoldOnce( ex3 )
    val unfolded4 = eh.unfoldOnce( ex4 )

//    println( unfolded1 )
//    println( unfolded2 )
//    println( unfolded3 )
//    println( unfolded4 )

    assert( unfolded1 === ex1 ) // Since the operator application appears incorrectly as a NameEx

//    def isNotOper( ex : TlaEx ) : Boolean = ex != NameEx( opName1 )

//    assert( RecursiveProcessor.globalTlaExProperty( isNotOper )( unfolded1 ) )


  }

  test("Unfold max") {
    val eh = newEh

    val opName1 = "X"
    val opName2 = "Y"

    val paramName = "a"

    val decl1 = tla.declOp( opName1, 1 )
    val decl2 = tla.declOp( opName2, tla.plus( paramName, tla.appOp(opName1) ), paramName )

    eh.extract( decl1, decl2 )
    val ex = tla.appOp( opName2, 0 )

    eh identify ex


    val unfolded1 = eh.unfoldOnce( ex )
    val unfolded2 = eh.unfoldOnce( unfolded1 )
    val unfoldedMax = eh.unfoldMax( ex )

    assert(
      ( ex !== unfolded1 ) &&
      ( unfolded1 !== unfolded2 ) &&
      ( unfolded2 === unfoldedMax )
    )

    def notOpers(ops: String*)( ex : TlaEx ) : Boolean = !ops.map( NameEx ).contains( ex )

    assert( RecursiveProcessor.globalTlaExProperty( notOpers(opName2) )(unfolded1) )
    assert( RecursiveProcessor.globalTlaExProperty( notOpers(opName1, opName2) )(unfolded2) )




  }
}