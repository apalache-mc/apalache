package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.actions._
import at.forsyte.apalache.tla.lir.plugins.Identifier
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import java.io._


/**
  * Tests for the assignment solver
  */
@RunWith(classOf[JUnitRunner])
class TestAssignments extends FunSuite {
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

//    val spec = assignments.apply(vars, phi4)


    val phi5 = makeLeafFull( "a", "b", true )
    val phi6 = makeLeafFull( "b", "a", true )
    val phi7 = OperEx( TlaBoolOper.and, phi5, phi6 )
    val phi8 = makeLeafFull( "b", "2", false )
    val phi9 = OperEx( TlaBoolOper.or, phi7, phi8 )
    val phi10 = makeLeafFull( "a", "1", false )
    val phi11 = OperEx( TlaBoolOper.and, phi9, phi10 )

    Identifier.identify( phi11 )


    val vars2 = Set[NameEx]( NameEx( "a" ), NameEx( "b" ) )


    val spec = assignments.apply(vars2, phi11 )

    //print( new File(".").getCanonicalPath )

    val pw = new PrintWriter(new File( "../test/tla/testSpec.smt2" ) )
    pw.write(spec)
    pw.close()

  }

}
