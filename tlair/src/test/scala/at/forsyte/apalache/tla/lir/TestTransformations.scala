package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.transformations._
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

  object Invariants {

    val NoAsAfter = new SimpleTransformationInvariant(
      "NoAsAfter",
      ( _, newEx ) => RecursiveProcessor.globalTlaExProperty {
        _ != n_a
      }( newEx )
    )

    val IsAlwaysIdentity = new SimpleTransformationInvariant(
      "IsAlwaysIdentity",
      ( originalEx, newEx ) => originalEx == newEx
    )

    val MonotonicallyBigger = new SimpleTransformationInvariant(
      "MonotonicallyBigger",
      ( originalEx, newEx ) => depthOf( originalEx ) <= depthOf( newEx )
    )

    val Impossible = new SimpleTransformationInvariant(
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
    val goodIdentity = new SimpleTransformation(
      identity,
      Invariants.IsAlwaysIdentity
    )

    val badIdentity = new SimpleTransformation(
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
    val listeners = Seq(
      Invariants.NoAsAfter
    )
    val aToB = ReplaceFixed( n_a, n_b, listeners : _* )
    val ex = ite( ge( n_p, int( 0 ) ), n_a, int( 0 ) )

    val aToBEx = aToB( n_a )
    assertThrows[InvariantViolation] {
      aToB( ex )
    }
  }

  test( "Test RecursiveTransformation" ) {
    val reduceDepth = new SimpleTransformation(
      {
        case OperEx( _, arg, _* ) => arg
        case ex@_ => ex
      }
    )

    val reduceDepthToOne = new RecursiveTransformation( reduceDepth )

    val ex = and( and( and( and( and( NullEx ) ) ) ) )

    val once = reduceDepth( ex )
    assert( once != NullEx )
    val fully = reduceDepthToOne( ex )
    assert( fully == NullEx )

  }

  test( "Test ConditionalTransformation" ) {
    val nullify = new SimpleTransformation(
      _ => NullEx
    )
    val nullifyOperators = new ConditionalTransformation(
      _.isInstanceOf[OperEx],
      nullify
    )
    val ex1 = n_a
    val ex2 = and( n_a, n_b )

    assert( nullify(ex1) == NullEx)
    assert( nullify(ex2) == NullEx)
    assert( nullifyOperators(ex1) != NullEx)
    assert( nullifyOperators(ex2) == NullEx)
  }
}
