package at.forsyte.apalache.tla.assignments

import java.io.{File, PrintWriter}

import at.forsyte.apalache.tla.lir.{TestingPredefs, TlaDecl, TlaEx, TlaOperDecl, TlaVarDecl, ValEx, Builder => bd}
import at.forsyte.apalache.tla.lir.plugins.UniqueDB
import at.forsyte.apalache.tla.imp.declarationsFromFile
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaTrue}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbTransPass extends FunSuite with TestingPredefs with TypeAliases {
  val testFolderPath = "src/test/resources/assignmentSolver/"

  def testFromNext( p_next : TlaEx ) : Seq[SymbTrans] = {
    testFromDecls( Seq( TlaOperDecl( "Next", List(), p_next ) ) )
  }

  def testFromDecls( p_decls : Seq[TlaDecl], p_next : String = "Next"   ) : Seq[SymbTrans]  = {
    UniqueDB.clear()

    new SymbolicTransitionPass()( p_decls, p_next )
  }

  def testFromFile( p_file : String, p_next : String = "Next" ) : Seq[SymbTrans] = {

    val decls = declarationsFromFile( testFolderPath + p_file )

    val ret = testFromDecls( decls, p_next )

//    val saveWriter = new PrintWriter( new File( testFolderPath + "SymbNexts" + p_file ) )

//    ret.foreach( x => saveWriter.println( "%s : \n %s\n".format( x._1.map( UniqueDB.get ) , x._2 ) ) )

//    saveWriter.close()

    ret
  }

  test( "Test Complete Spec return + unsat spec" ){
    UniqueDB.clear()
    val phi = bd.bool( false )
    val encoder = new AssignmentStrategyEncoder()
    val fullSpec = encoder( Set("x"), phi, p_complete = true )

    val spec = encoder( Set("x"), phi, p_complete = false)
    assert( fullSpec.nonEmpty )

    assert( (new SMTInterface())(spec, encoder.m_varSym).isEmpty )

  }

  test( "Test Next = single asgn, no connectives" ){
    val next = bd.primeInSingleton( n_x, n_S )

    val decls = Seq( TlaOperDecl( "Next", List(), next ), TlaVarDecl( "x" ) )

    val symbNexts = testFromDecls( decls )
    println( symbNexts.size )



  }

  test( "Test non-compliant SMT spec" ){
    val spec = "( declare-fun f ( Int ) Int )\n ( declare-fun g ( Int ) Int )\n" +
      "(assert ( = ( f 0 ) ( g 0 ) ) )"
    val smt = new SMTInterface()

    val strat = smt(spec, "X")

    assert( strat.isEmpty )

  }

  test( "Test no strat" ){
    val next = bd.primeInSingleton( n_x, n_S )

    val decls = Seq( TlaOperDecl( "Next", List(), next ), TlaVarDecl( "x" ), TlaVarDecl( "z" ) )

    assertThrows[AssignmentException]( testFromDecls( decls ) )

  }

  test( "Test no Next" ){
    val next = bd.primeInSingleton( n_x, n_S )

    val decls = Seq( TlaOperDecl( "Next", List(), next ), TlaVarDecl( "x" ) )

    assertThrows[AssignmentException]( testFromDecls( decls, "NotNext" ) )

  }

  test( "Test Selections" ){

    val symbNexts = testFromFile( "Selections.tla" )
    println( symbNexts.size )


  }

  test( "Test Paxos (simplified)" ){

    val symbNexts = testFromFile( "Paxos.tla" )
    println( symbNexts.size )

    printlns( symbNexts.map( _._2.toString ):_* )

  }

  test("Test ITE_CASE") {


    val symbNexts = testFromFile( "ITE_CASE.tla" )

  }

  test("Test EWD840") {


    val symbNexts = testFromFile( "EWD840.tla" )
    println( symbNexts.size )
  }

  test( "AST" ){

    val symbNexts = testFromFile( "ast.tla" )
    println( symbNexts.size )

  }

}
