package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.convenience._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner


@RunWith( classOf[JUnitRunner] )
class TestEnvHandler extends FunSuite with TestingPredefs {

  def newEh : EnvironmentHandler = EnvironmentHandlerGenerator.makeEH

  test( "Identification" ) {
    val eh = EnvironmentHandlerGenerator.makeEH

    val ex = tla.eql( 1, 0 )

    eh.identify( ex )
    eh.identify( ex )

    assert( eh.fullyIdentified( ex ) )
  }

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

  test( "ReplaceAll" ) {
    val eh = newEh

    val ex = tla.eql( tla.plus( 1, 1 ), 2 )
    val toReplace : TlaEx = 1
    val replaceWith : TlaEx = tla.appOp( "Cos", 0 )

    eh identify ex

    val replEx = eh.replaceAll( ex, toReplace, replaceWith )

    println(replEx)


  }
}