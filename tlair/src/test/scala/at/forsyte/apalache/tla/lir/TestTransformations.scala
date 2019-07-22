package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.transformations.impl._
import at.forsyte.apalache.tla.lir.transformations.standard._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestTransformations extends FunSuite with TestingPredefs {

  import Builder._

  private def depthOf( ex : TlaEx ) : Int = ex match {
    case OperEx( oper, args@_* ) => 1 + ( if ( args.nonEmpty ) ( args map depthOf ).max else 0 )
    case _ => 1
  }

  object Trackers {
    val NoTracker : TransformationTracker = new TransformationTracker {
      override def track( t : TlaExTransformation ) : TlaExTransformation = t
    }
  }

  object Invariants {
    private def noAs( ex : TlaEx ) : Boolean = ex match {
      case OperEx( _, args@_* ) =>
        args forall noAs
      case NameEx( n ) => n != "a"
      case _ => true
    }

    val NoAsAfter = new TransformationInvariant(
      "NoAsAfter",
      ( _, newEx ) => noAs( newEx )
    )

    val IsAlwaysIdentity = new TransformationInvariant(
      "IsAlwaysIdentity",
      ( originalEx, newEx ) => originalEx == newEx
    )

    val MonotonicallyBigger = new TransformationInvariant(
      "MonotonicallyBigger",
      ( originalEx, newEx ) => depthOf( originalEx ) <= depthOf( newEx )
    )

    val Impossible = new TransformationInvariant(
      "Impossible",
      ( _, _ ) => false
    )
  }

  test( "Test invariants" ) {
    assertThrows[InvariantViolation] {
      Invariants.Impossible.onTransformation( n_x, n_y )
    }
    val always = !Invariants.Impossible
    assert( always.holdsFor( n_x, n_y ) )

    assertThrows[InvariantViolation] {
      Invariants.MonotonicallyBigger.onTransformation( x_in_S, n_x )
    }
    assert( Invariants.MonotonicallyBigger.holdsFor( n_x, x_in_S ) )
  }

  test( "Test identity" ) {
    val goodIdentity = new TransformationImpl(
      identity,
      Invariants.IsAlwaysIdentity
    )

    val badIdentity = new TransformationImpl(
      identity,
      Invariants.Impossible
    )

    val exSeq = seq( 10 )

    val suppressedBadIdentity = badIdentity.suppressInvariantChecks

    exSeq foreach {
      e =>
        assert( e == goodIdentity( e ) )
        assert( e == suppressedBadIdentity( e ) )
        assertThrows[InvariantViolation] {
          badIdentity( e )
        }
    }
  }

  test( "Test ReplaceFixed" ) {

  }

  test( "Test RecursiveTransformation" ) {
    val reduceDepth = new TransformationImpl(
      {
        case OperEx( _, arg, _* ) => arg
        case ex@_ => ex
      }
    )

    val reduceDepthToOne = new RecursiveTransformationImpl( reduceDepth )

    val ex = and( and( and( and( and( NullEx, n_a ), n_b ), n_c ), n_d ), n_e )

    val once = reduceDepth( ex )
    assert( once != NullEx )
    val fully = reduceDepthToOne( ex )
    assert( fully == NullEx )

  }

  test( "Test EqualityAsContainment" ) {
    val transformation = EqualityAsContainment( Trackers.NoTracker )

    val ex1 = primeEq( n_x, n_y )
    val ex2 = or( primeEq( n_x, n_y ), ge( prime( n_x ), int( 0 ) ) )
    val ex3 = ite( primeEq( n_x, n_y ), primeEq( n_z, int( 0 ) ), primeEq( n_z, int( 1 ) ) )

    val expected1 = in( prime( n_x ), enumSet( n_y ) )
    val expected2 = or( in( prime( n_x ), enumSet( n_y ) ), ge( prime( n_x ), int( 0 ) ) )
    val expected3 = ite(
      in( prime( n_x ), enumSet( n_y ) ),
      in( prime( n_z ), enumSet( int( 0 ) ) ),
      in( prime( n_z ), enumSet( int( 1 ) ) )
    )

    val exs = Seq( ex1, ex2, ex3 )
    val expected = Seq( expected1, expected2, expected3 )
    val actual = exs map transformation
    assert( expected == actual )
  }

  test( "Test Inline" ) {
    val cDecl = declOp( "C", plus( n_x, int( 1 ) ), SimpleFormalParam( "x" ) )
    val operDecls = Seq(
      declOp( "A", appOp( n_B ) ),
      declOp( "B", n_c ),
      cDecl
    )

    val bodies = BodyMapFactory.makeFromDecls( operDecls )

    val transformation = Inline( bodies, Trackers.NoTracker )

    val ex1 = n_B
    val ex2 = appOp( n_B )
    val ex3 = n_A
    val ex4 = appOp( n_A )
    val ex5 = or( eql( int( 1 ), int( 0 ) ), ge( appDecl( cDecl, appOp( n_A ) ), int( 0 ) ) )
    val ex6 = letIn(
      appOp( NameEx( "X" ) ),
      declOp( "X", appOp( NameEx( "C" ), n_p ) )
    )

    val expected1 = n_B // Operators need to be called with apply
    val expected2 = n_c
    val expected3 = n_A // Operators need to be called with apply
    val expected4 = n_c
    val expected5 = or(
      eql( int( 1 ), int( 0 ) ),
      ge( plus( n_c, int( 1 ) ), int( 0 ) )
    )
    val expected6 = letIn(
      appOp( NameEx( "X" ) ),
      declOp( "X", plus( n_p, int( 1 ) ) )
    )

    val exs = Seq( ex1, ex2, ex3, ex4, ex5, ex6 )
    val expected = Seq( expected1, expected2, expected3, expected4, expected5, expected6 )
    val actual = exs map transformation

    assert( expected == actual )
  }

  test( "Test ExplicitLetIn" ) {
    val transformation = ExplicitLetIn( Trackers.NoTracker )

    val ex1 = n_x
    val ex2 = letIn( appOp( n_A ), declOp( "A", n_x ) )
    val ex3 = letIn( appOp( n_A, n_x ), declOp( "A", n_y, SimpleFormalParam( "y" ) ) )
    val ex4 =
      letIn(
        ite(
          ge( n_c, int( 0 ) ),
          letIn(
            appOp( NameEx( "Y" ) ),
            declOp( "Y", appOp( NameEx( "X" ), n_c, n_c ) )
          ),
          appOp( NameEx( "X" ), n_p, int( 3 ) )
        ),
        declOp( "X", ge( plus( n_a, n_b ), int( 0 ) ), "a", "b" )
      )

    val expected1 = n_x
    val expected2 = n_x
    val expected3 = n_x
    val expected4 =
      ite(
        ge( n_c, int( 0 ) ),
        ge( plus( n_c, n_c ), int( 0 ) ),
        ge( plus( n_p, int( 3 ) ), int( 0 ) )
      )

    val exs = Seq( ex1, ex2, ex3, ex4 )
    val expected = Seq( expected1, expected2, expected3, expected4 )
    val actual = exs map transformation

    assert( expected == actual )

  }

  test( "Test Prime" ) {
    val vars : Set[String] = Set(
      "x", "a"
    )
    val transformation = Prime( vars, Trackers.NoTracker )

    val pa1 = n_x -> prime( n_x )
    val pa2 = n_y -> n_y
    val pa3 = prime( n_x ) -> prime( n_x )
    val pa4 = and( n_x, n_y, prime( n_a ) ) -> and( prime( n_x ), n_y, prime( n_a ) )

    val expected = Seq(
      pa1, pa2, pa3, pa4
    )
    val cmp = expected map { case (k, v) =>
      (v, transformation( k ))
    }
    cmp foreach { case (ex, act) =>
      assert( ex == act )
    }
  }

  test( "Test ExplicitUnchanged" ) {
    val transformation = ExplicitUnchanged( Trackers.NoTracker )
    val inSing : TlaEx => TlaEx = ExplicitUnchanged.inSingleton

    val pa1 = n_x -> n_x
    val pa2 = unchanged( n_x ) -> inSing( n_x )
    val pa3 = and( n_x, unchanged( n_y ) ) -> and( n_x, inSing( n_y ) )
    val pa4 = letIn(
      appOp( NameEx( "X" ) ),
      declOp( "X", unchanged( n_x ) )
    ) -> letIn(
      appOp( NameEx( "X" ) ),
      declOp( "X", inSing( n_x ) )
    )
    val pa5 = unchangedTup( n_x, n_y ) -> and( inSing( n_x ), inSing( n_y ) )

    val expected = Seq(
      pa1, pa2, pa3, pa4, pa5
    )
    val cmp = expected map { case (k, v) =>
      (v, transformation( k ))
    }
    cmp foreach { case (ex, act) =>
      assert( ex == act )
    }
  }

}
