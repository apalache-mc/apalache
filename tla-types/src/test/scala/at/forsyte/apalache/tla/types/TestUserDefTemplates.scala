package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.smt.SmtTools.{And, BoolFormula, Or}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner


@RunWith( classOf[JUnitRunner] )
class TestUserDefTemplates extends FunSuite with TestingPredefs with BeforeAndAfter {

  import at.forsyte.apalache.tla.lir.{Builder => tla}

  var smtVarGen = new SmtVarGenerator

  val globNC : NameContext = Map(
    "x" -> smtVarGen.getFresh,
    "y" -> smtVarGen.getFresh
  )

  val emptyNC : NameContext = Map.empty

  val globBM : BodyMap     = Map.empty

  var udtg      = new UserDefinedTemplateGenerator( smtVarGen, globNC, globBM )

  before {
    smtVarGen = new SmtVarGenerator
    udtg = new UserDefinedTemplateGenerator( smtVarGen, globNC, globBM )
  }

  def transitiveEql( s : Seq[BoolFormula] )( a : SmtDatatype, b : SmtDatatype ) : Boolean =
    if ( s.contains( Eql( a, b ) ) || s.contains( Eql( b, a ) ) )
      true
    else {
      val self = transitiveEql( s )( _, _ )
      s.exists {
        case e@Eql( `a`, f ) =>
          transitiveEql( s.filterNot{ _ == e })( f, b )
        case e@Eql( `b`, f ) =>
          transitiveEql( s.filterNot{ _ == e })( f, a )
        case e@Eql( f, `a` ) =>
          transitiveEql( s.filterNot{ _ == e })( f, b )
        case e@Eql( f, `b` ) =>
          transitiveEql( s.filterNot{ _ == e })( a, f )
        case _ => false
      }
    }

  def flattenCond( s : Seq[BoolFormula] ) : Seq[BoolFormula] = s flatMap {
    case And( conds@_* ) => flattenCond( conds )
    case z => Seq( z )
  }

  test( "Literals" ) {
    val ex1 = tla.int( 1 )
    val ex2 = tla.str( "a" )
    val ex3 = tla.bool( true )
    val x = smtVarGen.getFresh

    val nbla1 = udtg.nabla( x, ex1, emptyNC )
    val nbla2 = udtg.nabla( x, ex2, emptyNC )
    val nbla3 = udtg.nabla( x, ex3, emptyNC )
    assert( nbla1.contains( Eql( x, int ) ) )
    assert( nbla2.contains( Eql( x, str ) ) )
    assert( nbla3.contains( Eql( x, bool ) ) )
  }

  test( "Variables/parameters" ) {
    val par1 = SimpleFormalParam( "p" )
    val par2 = OperFormalParam( "O", 2 )
    val ptVar1 = smtVarGen.getFresh
    val ptVar2 = smtVarGen.getFresh
    val xVar = smtVarGen.getFresh
    val yVar = smtVarGen.getFresh
    val m : NameContext = Map(
      "x" -> xVar,
      "y" -> yVar,
      par1.name -> ptVar1,
      par2.name -> ptVar2
    )

    val ex = tla.appOp( tla.name( par2.name ),
      tla.plus( n_x, n_y ),
      n_p
    )

    val x = smtVarGen.getFresh

    val nbla = udtg.nabla( x, ex, m)

    val flatNbla = flattenCond( nbla )

    /**
      * /\ vx =~= int
      * /\ vy =~= int
      * /\ \E tx .
      *   /\ x = tx
      *   /\ \E tO . \E i .
      *     /\ tO = [tup(i) => tx]
      *     /\ t0 =~= vO
      *     /\ \E a .
      *       /\ hasIndex(i,0,a)
      *       /\ a =~= int
      *     /\ \E a .
      *       /\ hasIndex(i,1,a)
      *       /\ a =~= vp
      */

    val transEq = transitiveEql( flatNbla )( _, _ )

    val assertCond =
      transEq( xVar, int ) &&
      transEq( yVar, int ) &&
      flatNbla.exists {
        case Eql( `x`, tx ) =>
          flatNbla.exists {
            case Eql( tO, oper( tup( i ), `tx` ) ) =>
              transEq( tO, ptVar2 ) &&
                flatNbla.contains( sizeOfEql( i, par2.arity ) ) &&
                flatNbla.exists {
                  case hasIndex( `i`, 0, fj ) =>
                    transEq( fj, int )
                  case _ => false
                } &&
                flatNbla.exists {
                  case hasIndex( `i`, 1, fj ) =>
                    transEq( fj, ptVar1 )
                  case _ => false
                }
            case _ => false
          }
        case _ => false

      }

    assert( assertCond )
  }

  test( "Test makeTemplate" ){
    val par1 = SimpleFormalParam( "p" )
    val par2 = OperFormalParam( "O", 2 )

    val body = tla.appOp( tla.name( par2.name ),
      tla.plus( n_x, n_y ),
      n_p
    )

    /**
      * X(p, O(_,_)) == O( x + y, p )
      */
    val operX = TlaOperDecl( "X", List( par1, par2 ), body )

    val e = smtVarGen.getFresh
    val ts@ List( t1, t2 ) = smtVarGen.getNFresh( operX.formalParams.length )

    val templ = udtg.makeTemplate( operX.formalParams, operX.body )
    val templApp = templ( e +: ts ).asInstanceOf[And]


    val condLst = flattenCond( templApp.args )

    /**
      * /\ vx =~= int
      * /\ vy =~= int
      * /\ \E tx .
      *   /\ x = tx
      *   /\ \E tO . \E i .
      *     /\ tO = [tup(i) => tx]
      *     /\ t0 =~= t2
      *     /\ \E a .
      *       /\ hasIndex(i,0,a)
      *       /\ a =~= int
      *     /\ \E a .
      *       /\ hasIndex(i,1,a)
      *       /\ a =~= t1
      */

    val transEq = transitiveEql( condLst )( _, _ )

    val assertCond =
      transEq( globNC( "x" ), int ) &&
      transEq( globNC( "y" ), int ) &&
        condLst.exists {
          case Eql( `e`, tx ) =>
            condLst.exists {
              case Eql( tO, oper( tup( i ), `tx` ) ) =>
                transEq( tO, t2 ) &&
                condLst.contains( sizeOfEql( i, par2.arity ) ) &&
                condLst.exists {
                  case hasIndex( `i`, 0, fj ) =>
                    transEq( fj, int )
                  case _ => false
                } &&
                condLst.exists {
                  case hasIndex( `i`, 1, fj ) =>
                    transEq( fj, t1 )
                  case _ => false
                }
              case _ => false
            }
          case _ => false

        }

    assert( assertCond )
  }

  test( "EXCEPT" ){

    /**
      * [ [a |-> 1, b |-> 2] EXCEPT !.a = 3 ]
      */

    val body = tla.except(
      tla.enumFun(
        tla.str( "a" ), tla.int( 1 ),
        tla.str( "b" ), tla.int( 2 )
      ),
      tla.tuple( tla.str( "a" ) ),
      tla.int( 3 )
    )

    val e = smtVarGen.getFresh

    val templ = udtg.makeTemplate( List.empty, body )
    val templApp = templ( e +: Nil ).asInstanceOf[And]

    val condLst = flattenCond( templApp.args )

    condLst foreach {
      case Or( _, And( args@_* ) ) =>
        args foreach println
      case hf: hasField =>
        println( hf )
      case e@Eql(_, r: rec) =>
        println( e )
      case _ =>
    }

  }


}
