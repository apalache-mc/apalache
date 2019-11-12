package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.{OperFormalParam, SimpleFormalParam, TestingPredefs, TlaOperDecl}
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestFSE extends FunSuite with TestingPredefs with BeforeAndAfter {

  import at.forsyte.apalache.tla.lir.{Builder => tla}

  var smtVarGen = new SmtVarGenerator
  var fse       = new FormalSignatureEncoder( smtVarGen )

  before {
    smtVarGen = new SmtVarGenerator
    fse       = new FormalSignatureEncoder( smtVarGen )
  }

  test( "Test paramType: SFP" ) {
    val p1 = SimpleFormalParam( "p1" )
    val p2 = SimpleFormalParam( "p2" )
    val pt1 = fse.paramType( p1 )
    val pt2 = fse.paramType( p2 )
    assert( pt1 == ReductionResult( SmtTypeVariable( 0 ), Seq.empty ) )
    assert( pt2 == ReductionResult( SmtTypeVariable( 1 ), Seq.empty ) )
  }

  test( "Test paramType: OFP" ) {
    val o1 = OperFormalParam( "O1", 1 )
    val o2 = OperFormalParam( "O2", 4 )
    val pt1 = fse.paramType( o1 )
    val pt2 = fse.paramType( o2 )

    /**
      * \E i . \E f .
      *   /\ t = oper( tup(i), f )
      *   /\ sizeOf(i) = |Oi|
      *   /\ \A j . \E fj . hasIndex( i, j, fj )
      */

    assert( List( (pt1, o1.arity), (pt2, o2.arity) ) forall {
      case (ReductionResult( oper( tup( i : SmtIntVariable ), _ ), phi ), arity) =>
        phi.contains( sizeOfEql( i, arity ) ) &&
          Range( 0, o1.arity ).forall { j =>
            phi.exists {
              case hasIndex( `i`, `j`, _ ) => true
              case _ => false
            }
          }
      case _ => false
    } )
  }

  test( "Test sig: Nullary" ){
    val op = tla.declOp( "X", n_x )
    val opSig = fse.sig( op.formalParams )

    assert( opSig.paramTypes == List( opSig.opType ) && opSig.constraints.isEmpty )
  }

  test( "Test sig: arity >0" ){
    // Simple
    val op1 = tla.declOp( "X", n_x, "p", "r"  )
    // H.O.
    val op2 = tla.declOp( "X", n_x, ("p",1), "r", ("s",2)  )

    def assertCond( opDecl: TlaOperDecl ) = fse.sig( opDecl.formalParams ) match {
      case SigTriple( oper( tup( i ), f ), parTs, phi ) if parTs.headOption.contains( f ) =>
        phi.contains( sizeOfEql( i, opDecl.formalParams.length ) ) &&
        parTs.tail.zipWithIndex.forall {
          case (t, j) =>
            phi.contains( hasIndex( i, j, t ) )
        }
      case _ => false
    }

    assert( assertCond( op1 ) )
    assert( assertCond( op2 ) )

  }


}
