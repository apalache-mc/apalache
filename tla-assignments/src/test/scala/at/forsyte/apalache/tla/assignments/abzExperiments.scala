package at.forsyte.apalache.tla.assignments

import java.io.{File, FileWriter, PrintWriter}

import at.forsyte.apalache.tla.imp._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.plugins.UniqueDB
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.{Builder => bd}

/**
  * Tests for the assignment solver
  */
@RunWith(classOf[JUnitRunner])
class abzExperiments extends FunSuite with TestingPredefs {
  val testFolderPath = "src/test/resources/abzExperiments/"

  type nameType = String
  type successFlag = Boolean
  type actoinCount = Int
  type stratSize = Option[Int]
  type symbTransCount = Option[Int]
  type runTime = Int
  type experimentData = (nameType, successFlag, actoinCount, stratSize, symbTransCount, runTime)

  val defaultData : experimentData = ("", false, 0, None, None, 0)

  def countNodes( p_ex: TlaEx ) : Int = {

    def leafJudge( ex: TlaEx ) : Boolean = {
      ex match {
        case OperEx( op, _* ) => op match{
          case TlaControlOper.ifThenElse |
            TlaBoolOper.and |
            TlaBoolOper.or |
            TlaBoolOper.exists => false
          case _ => true
        }
        case _ => true
      }
    }
    def leafFun( ex: TlaEx ) : Int = 1
    def parentFun( ex: TlaEx, chVals : Seq[Int] ) = chVals.sum + 1
    val default : Int = 1

    SpecHandler.bottomUpVal[Int](p_ex,leafJudge, leafFun, parentFun, default)

  }

  def runTest( p_file: String, p_next:String = "Next" ) : experimentData = {
    UniqueDB.clear()
    val converter = new Converter()

    val declsOld = declarationsFromFile( testFolderPath + p_file )
    val declsRenamed = OperatorHandler.uniqueVarRename( declsOld )
    val decls = declsRenamed.map(
      decl => decl match {
        case TlaOperDecl( name, params, body ) =>
          TlaOperDecl( name, params, converter.explicitLetIn( body ) )
        case _ => decl
      }
    )

    val vars = converter.getVars( decls : _* )
    val nextBody = findBodyOf( p_next, decls : _* )

    if ( nextBody.isNull || !nextBody.ID.valid ) {
      return defaultData.copy( _1 = p_file )
    }

    val cleaned = converter( nextBody, decls : _* )

    assert( cleaned.isDefined )
    assert( cleaned.get.ID.valid )

    val nNodes = countNodes( cleaned.get )

    val t0 = System.currentTimeMillis()

    val strat = assignmentSolver.getStrategy( vars, cleaned.get )

    if ( strat.isEmpty ) {
      val t1 = System.currentTimeMillis()
      return defaultData.copy( _1 = p_file, _3 = nNodes, _6 = ( t1 - t0 ).toInt )
    }

    val sn = assignmentSolver.getSymbNexts( cleaned.get, strat.get )

    if ( sn.isEmpty ) {
      val t1 = System.currentTimeMillis()
      return defaultData.copy( _1 = p_file, _3 = nNodes, _4 = strat.map( _.size ), _6 = ( t1 - t0 ).toInt )
    }

    val t1 = System.currentTimeMillis()
    (p_file, true, nNodes, strat.map( _.size ), Some( sn.length ), ( t1 - t0 ).toInt)
  }

  test( "Run All" ){
    val results = new File( testFolderPath ).listFiles().map( x => runTest( x.getName ) )

    val resultsLocation = "src/test/resources/abzResultsTable.csv"

    val separator = ","

    val firstLine = ("Specification%1$sSuccessful Termination%1$s" +
      "Number of Nodes%1$sSize of Assignment Strategy%1$sumber of Symbolic Transitions" +
      "%1$sRuntime (ms)\n").format( separator )

    val pw = new FileWriter( new File( resultsLocation ) )
    pw.write( firstLine)

    def printTup( data : experimentData ) : String = {
      "%s%7$s%s%7$s%s%7$s%s%7$s%s%7$s%s\n".format(
        data._1.replace("_", "$\\_$"),
        data._2,
        data._3,
        data._4.getOrElse(None),
        data._5.getOrElse(None),
        data._6,
        separator
      )

    }
    results.foreach( x => pw.write( printTup( x ) ) )

    pw.close()
  }

}
