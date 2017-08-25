package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.actions._
import at.forsyte.apalache.tla.lir.plugins.Identifier
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

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
    def makeLeaf( lhs: String ) : OperEx = makeLeafFull(lhs, lhs, false )


    def makeLeafBranches( oper: TlaOper, names: String* ) : OperEx = {
      return OperEx( oper, names.map( makeLeaf ):_* )
    }

    def makeLeafBranchesBoth( oper: TlaOper, names: (String,String,Boolean)* ) : OperEx = {
      return OperEx( oper, names.map( pa => makeLeafFull( pa._1, pa._2, pa._3 ) ):_* )
    }


    val Phi1 = makeLeafBranches( TlaBoolOper.and, "0", "1" )

    val Phi2 = OperEx(  TlaBoolOper.and,
                        makeLeafBranches( TlaBoolOper.or, "2", "3" ),
                        makeLeafBranches( TlaBoolOper.or, "4", "5" )
    )

    val Phi3 =
      OperEx(
        TlaBoolOper.or,
        Phi1,
        Phi2
    )

    val Phi4=
      OperEx(
        TlaBoolOper.and,
        Phi3,
        makeLeafBranches( TlaBoolOper.and, "6", "7" )


      )

    Identifier.identify( Phi4 )

    assignments.apply(vars, Phi4)

  }

}
