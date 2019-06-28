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

    val NoAsAfter = new TransformationInvariant(
      "NoAsAfter",
      ( _, newEx ) => RecursiveProcessor.globalTlaExProperty {
        _ != n_a
      }( newEx )
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
    val goodIdentity = new Transformation(
      identity,
      Invariants.IsAlwaysIdentity
    )

    val badIdentity = new Transformation(
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
    val reduceDepth = new Transformation(
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
}
