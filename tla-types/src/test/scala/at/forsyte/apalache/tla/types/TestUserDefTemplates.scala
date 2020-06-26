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

  val limits = SpecLimits( 7, Set("a","b","c","d","e","f","x","y") )

  var smtVarGen = new SmtVarGenerator

  val globBind : GlobalBinding = Map(
    "x" -> smtVarGen.getFresh,
    "y" -> smtVarGen.getFresh
  )

  val emptyBind : Binding = Map.empty

  val globBM : BodyMap = Map.empty

  var udtg = new UserDefinedTemplateGenerator( limits, smtVarGen, globBind, globBM )

  before {
    smtVarGen = new SmtVarGenerator
    udtg = new UserDefinedTemplateGenerator( limits, smtVarGen, globBind, globBM )
  }

  def transitiveEql( s : Seq[BoolFormula] )( a : SmtDatatype, b : SmtDatatype ) : Boolean =
    if ( s.contains( Eql( a, b ) ) || s.contains( Eql( b, a ) ) )
      true
    else {
      val self = transitiveEql( s )( _, _ )
      s.exists {
        case e@Eql( `a`, f ) =>
          transitiveEql( s.filterNot {
            _ == e
          } )( f, b )
        case e@Eql( `b`, f ) =>
          transitiveEql( s.filterNot {
            _ == e
          } )( f, a )
        case e@Eql( f, `a` ) =>
          transitiveEql( s.filterNot {
            _ == e
          } )( f, b )
        case e@Eql( f, `b` ) =>
          transitiveEql( s.filterNot {
            _ == e
          } )( a, f )
        case _ => false
      }
    }

  def flattenCond( s : Seq[BoolFormula] ) : Seq[BoolFormula] = s flatMap {
    case And( conds@_* ) => flattenCond( conds )
    case z => Seq( z )
  }

  test( "Wrong arity" ) {
    val ex = tla.plus( n_x, n_y )

    val templateArgs = smtVarGen.getNFresh( 2 )
    val template = udtg.makeTemplate( TlaOperDecl( "X", List.empty, ex ) )
    assertThrows[AssertionError] {
      template( templateArgs )
    }
    assertThrows[IllegalArgumentException] {
      template( List.empty )
    }
  }

  test( "Unsupported expr." ) {
    assertThrows[IllegalArgumentException] {
      udtg.isType( int, NullEx, Map.empty )
    }
  }

  test( "Literals" ) {
    val ex1 = tla.int( 1 )
    val ex2 = tla.str( "a" )
    val ex3 = tla.bool( true )
    val x = smtVarGen.getFresh

    val typeConstr1 = udtg.isType( x, ex1, emptyBind )
    val typeConstr2 = udtg.isType( x, ex2, emptyBind )
    val typeConstr3 = udtg.isType( x, ex3, emptyBind )
    assert( typeConstr1.contains( Eql( x, int ) ) )
    assert( typeConstr2.contains( Eql( x, str ) ) )
    assert( typeConstr3.contains( Eql( x, bool ) ) )
  }

  test( "Variables/parameters" ) {
    val par1 = SimpleFormalParam( "p" )
    val par2 = OperFormalParam( "O", 2 )
    val ptVar1 = smtVarGen.getFresh
    val ptVar2 = smtVarGen.getFresh
    val xVar = smtVarGen.getFresh
    val yVar = smtVarGen.getFresh
    val nu : Binding = Map(
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

    val typeConstr = udtg.isType( x, ex, nu )

    val flatConstr = flattenCond( typeConstr )

    /**
      * /\ vx =~= int
      * /\ vy =~= int
      * /\ vO =~= oper( tup( 2, int, vp, ... ), x )
            */

    val transEq = transitiveEql( flatConstr )( _, _ )

    val assertCond =
      transEq( xVar, int ) &&
        transEq( yVar, int ) &&
        flatConstr.exists {
          case Eql( f1, oper( tup(SmtKnownInt(2), idxs), f4 ) ) =>
            val List(f2,f3,_*) = idxs
            transEq(f1, ptVar2) &&
            transEq( f2, int ) &&
            transEq( f3, ptVar1) &&
            transEq( f4, x )
          case _ => false

        }

    assert( assertCond )
  }

  test( "Test makeTemplate" ) {
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
    val ts@List( t1, t2 ) = smtVarGen.getNFresh( operX.formalParams.length )

    val templ = udtg.makeTemplate( operX )
    val templApp = templ( e +: ts ).asInstanceOf[And]


    val condLst = flattenCond( templApp.args )

    /**
      * /\ vx =~= int
      * /\ vy =~= int
      * /\ t2 =~= oper( tup( 2, int, t1, ... ), e )
      */

    val transEq = transitiveEql( condLst )( _, _ )

    val assertCond =
      transEq( globBind( "x" ), int ) &&
        transEq( globBind( "y" ), int ) &&
        condLst.exists {
          case Eql( f1, oper( tup(SmtKnownInt(2), idxs), f4 ) ) =>
            val List(f2,f3,_*) = idxs
            transEq(f1, t2) &&
              transEq( f2, int ) &&
              transEq( f3, t1) &&
              transEq( f4, e )
          case _ => false

        }


    assert( assertCond )
  }

  // TODO: update with except-for-seq
//  ignore( "Test EXCEPT return type contains all fields" ) {
//
//    /**
//      * [ [a |-> 1, b |-> 2] EXCEPT !.a = 3 ]
//      */
//    val body = tla.except(
//      tla.enumFun(
//        tla.str( "a" ), tla.int( 1 ),
//        tla.str( "b" ), tla.int( 2 )
//      ),
//      tla.tuple( tla.str( "a" ) ),
//      tla.int( 3 )
//    )
//
//    val e = smtVarGen.getFresh
//
//    val templ = udtg.makeTemplate( TlaOperDecl( "X", List.empty, body ) )
//    val templApp = templ( e +: Nil ).asInstanceOf[And]
//
//    // We anticipate the Rec-side of Or
//    def oracleDecideOr( bf : BoolFormula ) : BoolFormula = bf match {
//      case Or( _, b ) => b
//      case x => x
//    }
//
//    val condLst = flattenCond( templApp.args map oracleDecideOr )
//
//    /**
//      * \E i .
//      *   /\ e = rec(i)
//      *   /\ hasField( i, "b", int )
//      */
//    val assertCond = condLst exists {
//      case Eql( t, recOld( i ) ) => condLst exists {
//        case hasField( `i`, "b", p ) =>
//          transitiveEql( condLst )( t, e ) && transitiveEql( condLst )( p, int )
//        case _ => false
//      }
//      case _ => false
//    }
//
//    assert( assertCond )
//  }
//
//  test( "Test LET-IN" ) {
//    // LET A == 1 IN A
//    val aDecl = tla.declOp( "A", tla.int( 1 ) )
//    val body = tla.letIn( tla.appDecl( aDecl ), aDecl )
//    val e = smtVarGen.getFresh
//
//    val templ = udtg.makeTemplate( TlaOperDecl( "X", List.empty, body ) )
//    val templApp = templ( e +: Nil ).asInstanceOf[And]
//
//    val condLst = flattenCond( templApp.args )
//
//    val assertCond = condLst exists {
//      case Eql( t, int ) => transitiveEql( condLst )( t, e )
//      case _ => false
//    }
//
//    assert( assertCond )
//  }
}
