package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.{OperFormalParam, SimpleFormalParam, TestingPredefs, TlaOperDecl}
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestFSE extends FunSuite with TestingPredefs with BeforeAndAfter {

  import at.forsyte.apalache.tla.lir.{Builder => tla}

  val limits = SpecLimits( 7, Set("a","b","c","d","e","f","x","y") )
  var smtVarGen = new SmtVarGenerator
  var fse       = new FormalSignatureEncoder( limits, smtVarGen )

  before {
    smtVarGen = new SmtVarGenerator
    fse       = new FormalSignatureEncoder( limits, smtVarGen )
  }

  test( "Test paramType: SFP" ) {
    val f = smtVarGen.getFresh
    val p1 = SimpleFormalParam( "p1" )
    val pt1 = fse.paramType( p1 )( f )
    assert( pt1.isEmpty )
  }

  test( "Test paramType: OFP" ) {
    val f = smtVarGen.getFresh
    val o1 = OperFormalParam( "O1", 1 )
    val o2 = OperFormalParam( "O2", 4 )
    val pt1 = fse.paramType( o1 )( f )
    val pt2 = fse.paramType( o2 )( f )

    assert( List( (pt1, o1.arity), (pt2, o2.arity) ) forall {
      case (Seq( Eql( `f`, oper( tup( SmtKnownInt( i ), _ ), _ ) ) ), arity) =>
        i == arity
      case _ => false
    } )
  }

  test( "Test sig: Nullary" ){
    val op = tla.declOp( "X", n_x )
    val opSig = fse.sig( op.formalParams )
    val of@List(o, f) = smtVarGen.getNFresh(2)

    val sigConstraints = opSig( of )

    assert(
      sigConstraints match {
        case Seq( Eql( `o`, oper( tup( size, idxs ), `f` ) ) ) =>
          size == SmtKnownInt( op.formalParams.size )
        case _ => false
      }
    )

  }

  test( "Test sig: arity >0" ){
    // Simple
    val op1 = tla.declOp( "X", n_x, "p", "r"  )
    // H.O.
    val op2 = tla.declOp( "X", n_x, ("p",1), "r", ("s",2)  )

    def assertCond( opDecl: TlaOperDecl ) = {
      val of@List(o, f) = smtVarGen.getNFresh(2)
      val ts = smtVarGen.getNFresh(opDecl.formalParams.size)

      val res = fse.sig( opDecl.formalParams )(of ++ ts)
      res match {
        case Eql( `o`, oper( tup( size, idxs ), `f` ) ) +: constraints =>
          val hoParams = opDecl.formalParams.zip( ts ).filter( pa => pa._1.isInstanceOf[OperFormalParam])
          size == SmtKnownInt( opDecl.formalParams.size ) &&
            constraints.zip( hoParams ).forall {
              case ( c, (OperFormalParam(_,arity), ti) ) => c match {
                case Eql( `ti`, oper( tup( SmtKnownInt(`arity`), _ ), _ ) ) => true
                case _ => false
              }
              case _ => false
            }
        case _ => false
      }
    }

    assert( assertCond( op1 ) )
    assert( assertCond( op2 ) )

  }


}
