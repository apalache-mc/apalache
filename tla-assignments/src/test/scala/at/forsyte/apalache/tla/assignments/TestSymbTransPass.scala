package at.forsyte.apalache.tla.assignments

import java.io.{File, PrintWriter}

import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.lir.plugins.UniqueDB
import at.forsyte.apalache.tla.imp.declarationsFromFile
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbTransPass extends FunSuite with TestingPredefs with TypeAliases {
  val testFolderPath = "src/test/resources/assignmentSolver/"

  def testFromFile( p_file : String, p_next : String = "Next" ) : Seq[SymbTrans] = {
    UniqueDB.clear()

    val decls = declarationsFromFile( testFolderPath + p_file )

    val ret = SymbolicTransitionPass( decls )

//    val saveWriter = new PrintWriter( new File( testFolderPath + "SymbNexts" + p_file ) )

//    ret.foreach( x => saveWriter.println( "%s : \n %s\n".format( x._1.map( UniqueDB.get ) , x._2 ) ) )

//    saveWriter.close()

    ret
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
