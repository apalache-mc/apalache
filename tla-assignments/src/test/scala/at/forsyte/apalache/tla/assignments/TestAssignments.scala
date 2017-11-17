package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.plugins.Identifier

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.io.Source


/**
  * Tests for the assignment solver
  */
@RunWith(classOf[JUnitRunner])
class TestAssignments extends FunSuite {
  val testFolderPath = "src/test/resources/" // "../test/tla/"

  test("Check dependency set computation") {

    val vars : Set[NameEx] = Range(0,8).map( x => NameEx( x.toString ) ).toSet

    def makeLeafFull( lhs: String, rhs: String, primed : Boolean ) : OperEx = {
      return OperEx(
        TlaSetOper.in,
        OperEx(
          TlaActionOper.prime,
          NameEx( lhs )
        ),
        if (primed)
          OperEx(
            TlaActionOper.prime,
            NameEx( rhs )
          )
        else NameEx(rhs)
      )
    }
    def makeLeaf( lhs: String ) : OperEx = makeLeafFull( lhs, lhs , false )
    def makeLeafBranches( oper: TlaOper, names: String* ) : OperEx = {
      return OperEx( oper, names.map( makeLeaf ):_* )
    }
    def makeLeafBranchesBoth( oper: TlaOper, names: (String,String,Boolean)* ) : OperEx = {
      return OperEx( oper, names.map( pa => makeLeafFull( pa._1, pa._2, pa._3 ) ):_* )
    }

    val phi1 = makeLeafBranches( TlaBoolOper.and, "0", "1" )
    val phi2 = OperEx(  TlaBoolOper.and,
                        makeLeafBranches( TlaBoolOper.or, "2", "3" ),
                        makeLeafBranches( TlaBoolOper.or, "4", "5" )
    )
    val phi3 =
      OperEx(
        TlaBoolOper.or,
        phi1,
        phi2
    )
    val phi4=
      OperEx(
        TlaBoolOper.and,
        phi3,
        makeLeafBranches( TlaBoolOper.and, "6", "7" )
      )

    Identifier.identify( phi4 )

    val importer = new SanyImporter()

    val name1 = "assignmentTest1"

    val src1 = Source.fromFile(testFolderPath + name1 + ".tla")

    val (rootName1, modules1) = importer.loadFromSource(name1, Source.fromFile(testFolderPath + name1 + ".tla") )
    val phi_ =
      modules1(rootName1).declarations.find { _.name == "Next"} match {
        case Some(d: TlaOperDecl) =>
          d.body match {
            case OperEx( op, agrs@_* ) => d.body.asInstanceOf[OperEx]
            case _ => NullEx
          }

        case _ =>
          NullEx
      }

    val vars1 = (
      for {decl <- modules1(rootName1).declarations if decl.isInstanceOf[TlaVarDecl]}
        yield NameEx(decl.name)
      ).toSet

    assert( phi_ != NullEx )
    val phi = phi_.asInstanceOf[OperEx]

    Identifier.identify( phi )

    val fname = testFolderPath + name1 + ".smt2"

    val ret =  assignmentSolver.getOrder(vars1, phi, fname )

    assert( ret.nonEmpty )

//    ret.get.foreach( pa => println( "%s -> %s".format( pa._1.id, pa._2 ) ) )

  }

  test("Check sanitization") {
    val fileName = "assignmentTest2.tla"
    val extracted = sanitizer(testFolderPath + fileName)
    assert(extracted.isDefined)
    val (before, after) = extracted.get
//    println( "%s \n -> \n %s".format( before, after ) )

    val bd = Builder

    val expected =
      bd.and(
        bd.or(
          bd.and(
            bd.in( bd.prime( "a" ), bd.enumSet( bd.prime( "b" ) ) ),
            bd.in( bd.prime( "b" ), bd.enumSet( bd.prime( "a" ) ) )
//            bd.primeEq( "a", "b" ),
//            bd.primeEq( "b", "a" )
          ),
          bd.in( bd.prime( "b" ), bd.enumSet( bd.int( 2 ) ) )
//          bd.primeEq( "b", 2)
        ),
        bd.in( bd.prime( "a" ), bd.enumSet( bd.int( 1 ) ) )
//        bd.primeEq( "a", 1 )
      )

    assert(after == expected)
  }

}
