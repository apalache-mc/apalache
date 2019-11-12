package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.oper.{FixedArity, Interpretation, OperArity, TlaOper}
import at.forsyte.apalache.tla.lir.{OperEx, TestingPredefs}
import at.forsyte.apalache.tla.lir.smt.SmtTools.{And, Or}
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestBuiltinTemplates extends FunSuite with TestingPredefs with BeforeAndAfter {
  var smtVarGen = new SmtVarGenerator
  var templateGen = new BuiltinTemplateGenerator(smtVarGen)

  before {
    smtVarGen = new SmtVarGenerator
    templateGen = new BuiltinTemplateGenerator(smtVarGen)
  }

  import at.forsyte.apalache.tla.lir.{Builder => tla}

  test( "Wrong arity" ){
    val ex = tla.plus( n_x, n_y )

    val templateArgs = smtVarGen.getNFresh( 2 )
    val template = templateGen.makeTemplate( ex )
    assertThrows[AssertionError] {
     template( templateArgs )
    }
    assertThrows[IllegalArgumentException] {
      template( List.empty )
    }
  }

  test( "No signature" ){
    val bogusOper = new TlaOper {

      override def precedence : (Int, Int) = (0, 0)

      override def arity : OperArity = FixedArity( 0 )

      override def interpretation : Interpretation.Value = Interpretation.User

      override def name : String = "bogus"
    }
    val ex = OperEx( bogusOper )
    val templateArgs = smtVarGen.getNFresh( 1 )
    val template = templateGen.makeTemplate( ex )

    assertThrows[IllegalArgumentException]{
      template( templateArgs )
    }
  }

  test( "Simple operator: +" ){
    val ex = tla.plus( n_x, n_y )

    val templateArgs@List(e,t1,t2) = smtVarGen.getNFresh( 3 )
    val template = templateGen.makeTemplate( ex )
    val templateApp = template( templateArgs )

    assert( templateApp.isInstanceOf[And] )
    val andCast = templateApp.asInstanceOf[And]
    assert( andCast.args.contains( Eql( e, int ) ) )
    assert( andCast.args.contains( Eql( t1, int ) ) )
    assert( andCast.args.contains( Eql( t2, int ) ) )

  }

  test( "Poly operator: =" ){
    val ex = tla.eql( n_x, n_y )

    val templateArgs@List(e,t1,t2) = smtVarGen.getNFresh( 3 )
    val template = templateGen.makeTemplate( ex )
    val templateApp = template( templateArgs )

    assert( templateApp.isInstanceOf[And] )
    val andCast = templateApp.asInstanceOf[And]
    assert( andCast.args.contains( Eql( e, bool ) ) )
    assert(
      andCast.args.exists {
        case Eql( a, b ) if a == t1 => andCast.args.exists {
          case Eql( c, d ) if c == t2 => b == d
          case _ => false
        }
        case _ => false
      }
    )
  }

  test( "Poly operator: \\cup" ){
    val ex = tla.cup( n_x, n_y )

    val templateArgs = smtVarGen.getNFresh( 3 )
    val template = templateGen.makeTemplate( ex )
    val templateApp = template( templateArgs )

    assert( templateApp.isInstanceOf[And] )
    val andCast = templateApp.asInstanceOf[And]
    assert(
      andCast.args.exists {
        case Eql( _, t ) => andCast.args.forall {
          case Eql( _, x @ set( SmtTypeVariable( _ ) )  ) => t == x
          case _ => true
        }
        case _ => false
      }
    )
  }

  test( "Poly operator: \\times" ){
    val ex = tla.times( n_a, n_b, n_c, n_d )

    val templateArgs @ e +: ts = smtVarGen.getNFresh( 1 + ex.args.length )
    val tmap = ts.zipWithIndex.map( pa => pa._2 -> pa._1 ).toMap
    val template = templateGen.makeTemplate( ex )
    val templateApp = template( templateArgs )

    assert( templateApp.isInstanceOf[And] )
    val andCast = templateApp.asInstanceOf[And]

    /**
      * \E i .
      *   /\ e = set( tup( i ) )
      *   /\ sizeOfEql( i, |ts| )
      *   /\ \A j . \E k .
      *     /\ t(j) = set( f(k) )
      *     /\ hasIndex( i, j, f(k) )
      */

    assert(
      andCast.args.exists {
        case Eql( `e`, set( tup( i ) ) ) =>
          andCast.args.exists {
            case sizeOfEql( `i`, k ) => k == ts.length
            case _ => false
          } &&
            tmap.forall { case (j, tj) =>
              andCast.args.exists {
                case Eql( `tj`, set( f ) ) =>
                  andCast.args.contains( hasIndex( i, j, f ) )
                case _ => false
              }
            }
        case _ => false
      }
    )
  }

  test("Overloaded operator: EXCEPT"){

    val ex1 = tla.except( n_x, tla.tuple( tla.str( "a" ) ), tla.str( "b" ) )
    val templateArgs1 @ e1 +: ts1 = smtVarGen.getNFresh( 1 + ex1.args.length )
    val tmap1 = ts1.zipWithIndex.map( pa => pa._2 -> pa._1 ).toMap
    val template1 = templateGen.makeTemplate( ex1 )
    val templateApp1 = template1( templateArgs1 )

    /**
      * Let ts1 = List(t11,t12,t13)
      *
      * \E i .
      *   /\ e1 = rec(i)
      *   /\ \E t .
      *     /\ hasField( i, "a", t )
      *     /\ t13 = t
      */
    val assertCond1 =
      templateApp1 match {
        case Or( _, And( args@_* ) ) => args exists {
          case Eql( `e1`, rec( i ) ) => args exists {
            case hasField( `i`, "a", t2 ) => args exists {
              case Eql( t1, `t2` ) => ts1.reverse.headOption contains t1
              case _ => false
            }
            case _ => false
          }
          case _ => false
        }
        case _ => false
      }

    assert( assertCond1 )

    val ex2 = tla.except(
      n_x,
      tla.tuple( tla.str( "a" ), tla.str( "b" ) ), 0,
      tla.tuple( tla.str( "a" ), tla.str( "c" ) ), tla.emptySet(),
      tla.tuple( tla.str( "e" ), tla.str( "f" ) ), tla.tuple( tla.int(1), tla.int(2) )
    )
    val templateArgs2 @ e2 +: ts2 = smtVarGen.getNFresh( 1 + ex2.args.length )
    val tmap2 = ts2.zipWithIndex.map( pa => pa._2 -> pa._1 ).toMap
    val template2 = templateGen.makeTemplate( ex2 )
    val templateApp2 = template2( templateArgs2 )

    /**
      * Let ts2 = List(t21,t22,t23,t24,t25,t26,t27)
      *
      * \E i .
      *   /\ e2 = rec(i)
      *   /\ \E j .
      *     /\ hasField( i, "a", rec(j) )
      *     /\ \E x .
      *       /\ hasField(j, "c", x)
      *       /\ x = t25
      */
    val assertCond2 =
      templateApp2 match {
        case Or( _, And( args@_* ) ) => args exists {
          case Eql( `e2`, rec( i ) ) => args.exists {
            case hasField( `i`, "a", rec( j ) ) => args exists {
              case hasField( `j`, "c", x ) => args exists {
                case Eql( y, `x` ) => ts2.take( 5 ).reverse.headOption contains y
                case _ => false
              }
              case _ => false
            }
            case _ => false
          }
          case _ => false
        }
        case _ => false
      }

    assert( assertCond2 )
    
  }

}
