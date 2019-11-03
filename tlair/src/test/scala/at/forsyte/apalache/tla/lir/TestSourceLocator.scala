package at.forsyte.apalache.tla.lir

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.Builder._
import at.forsyte.apalache.tla.lir.aux._
import at.forsyte.apalache.tla.lir.predef.{TlaIntSet, TlaStrSet}
import at.forsyte.apalache.tla.lir.src.{SourceLocation, SourcePosition, SourceRegion}
import at.forsyte.apalache.tla.lir.storage.{BodyMapFactory, ChangeListener, SourceLocator, SourceMap}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationListener}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard._

import scala.collection.mutable


@RunWith( classOf[JUnitRunner] )
class TestSourceLocator extends FunSuite with TestingPredefs {

  val decl1 = declOp( "plus", plus( n_a, n_b ), "a", "b" )
  val decl2 = declOp( "App", appOp( "X", n_p ), ("X", 1), "p" )

  val decls = List(
    decl1,
    decl2
  )

  val bodyMap = BodyMapFactory.makeFromDecls( decls )

  val ex1 = and( prime( n_x ), n_y )
  val ex2 = letIn(
    ge( appOp( n_A, int( 1 ) ), int( 0 ) ),
    declOp( "A", plus( n_p, int( 1 ) ), "p" )
  )
  val ex3 = appDecl( decl1, n_x, int( 1 ) )
  val ex4 = letIn(
    ite( n_y, appDecl( decl2, "I", int( 0 ) ), falseEx ),
    declOp( "I", n_p, "p" )
  )
  val ex5 =
    letIn(
      letIn(
        letIn(
          appOp( "C", appOp( "D" ) ),
          declOp( "D", n_x )
        ),
        declOp( "B", n_b ),
        declOp( "C", appOp( n_A, n_p, appOp( "B" ) ), "p" )
      ),
      declOp( "A", appOp( "IntentionallyUndefinedOper", n_p, n_q ), "p", "q" )
    )
  val ex6 = unchanged( n_x )
  val ex7 = unchangedTup( n_x, n_y )
  val ex8 =
    withType(
      enumFun( str( "x" ), int( 1 ) ),
      enumFun(
        str( "x" ), ValEx( TlaIntSet ),
        str( "y" ), enumSet( ValEx( TlaStrSet ) )
      )
    )
  val ex9 = appFun( enumFun( str( "x" ), int( 1 ) ), str( "x" ) )

  val exs = List(
    ex1,
    ex2,
    ex3,
    ex4,
    ex5,
    ex6,
    ex7,
    ex8,
    ex9
  )

  def generateLoc( uid : UID ) =
    new SourceLocation(
      "filename",
      new SourceRegion(
        new SourcePosition( uid.id.toInt ),
        new SourcePosition( uid.id.toInt )
      )
    )

  // Arbitrary assignment, all exs get a unique position equal to their UID
  val sourceMap : SourceMap =
    ( ( exs.map( allUidsBelow ) ++ decls.map( _.body ).map( allUidsBelow ) ).foldLeft( Set.empty[UID] ) {
      _ ++ _
    } map {
      x => x -> generateLoc( x )
    } ).toMap

  val exMap = new mutable.HashMap[UID, TlaEx]()

  val mapListener = new TransformationListener {
    override def onTransformation( originalEx : TlaEx, newEx : TlaEx ) : Unit = {
      exMap.update( originalEx.ID, originalEx )
      exMap.update( newEx.ID, newEx )
    }
  }

  val changeListener = new ChangeListener()
  val tracker        = TrackerWithListeners( changeListener, mapListener )

  val locator = SourceLocator( sourceMap, changeListener )

  def testTransformation( t : TlaExTransformation ) : Unit = {
    val post = exs map t
    val postIds = post.map( allUidsBelow ).foldLeft( Set.empty[UID] ) {
      _ ++ _
    }

    val failures = postIds.filterNot( i => locator.sourceOf( i ).nonEmpty )
    assert( failures.isEmpty )
  }

  test( "Test DeepCopy" ) {
    val transformation = DeepCopy( tracker )

    testTransformation( transformation )
  }

  test( "Test EqualityAsContainment" ) {
    val transformation = PrimedEqualityToMembership( tracker )

    testTransformation( transformation )
  }

  test( "Test ExplicitLetIn" ) {
    val transformation = LetInExpander( tracker, keepNullary = false )

    testTransformation( transformation )
  }

  test( "Test Flatten" ) {
    val transformation = Flatten( tracker )

    testTransformation( transformation )
  }

  test( "Test IncrementalRenaming" ) {
    val transformation = new IncrementalRenaming( tracker )

    testTransformation( transformation )
  }

  test( "Test Inline" ) {
    val transformation = InlinerOfUserOper( bodyMap, tracker )

    testTransformation( transformation )
  }

  test( "Test NoOp" ) {
    val transformation = tracker.track {
      identity
    }

    testTransformation( transformation )
  }

  test( "Test Prime" ) {
    val vars = Set( "x", "y" )
    val transformation = Prime( vars, tracker )

    testTransformation( transformation )
  }

  test( "Test PruneApalacheAnnotations" ) {
    val transformation = PruneApalacheAnnotations( tracker )

    testTransformation( transformation )
  }

  test( "Test SimplifyRecordAccess" ) {
    val transformation = SimplifyRecordAccess( tracker )

    testTransformation( transformation )
  }

}
