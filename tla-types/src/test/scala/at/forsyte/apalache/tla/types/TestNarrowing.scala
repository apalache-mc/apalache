package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.types.smt.IndexEvaluator
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestNarrowing extends FunSuite with TestingPredefs with BeforeAndAfter {

  val trivialIdxEval : IndexEvaluator = i => i

  test( "No hasField constraints" ){
    val narrower = new TypeNarrower( Map.empty, trivialIdxEval )
    val recT = RecT( Map( "a" -> IntT, "b" -> StrT ) )
    val expected = RecT( Map.empty )
    val actual = narrower.narrow( recT, 0 )

    assert( expected == actual )
  }

  test( "One spurious field" ){
    val observed = Map(
      SmtIntVariable( 0 ) -> Set("a","b")
    )

    val narrower = new TypeNarrower( observed, trivialIdxEval )
    val recT = RecT( Map( "a" -> IntT, "b" -> StrT, "c" -> TupT( IntT, IntT ) ) )
    val expected = RecT( Map( "a" -> IntT, "b" -> StrT ) )
    val actual = narrower.narrow( recT, 0 )

    assert( expected == actual )
  }

  test( "Two records" ){
    val constraints = Map(
      SmtIntVariable(0) -> Set("a","b"),
      SmtIntVariable(1) -> Set("c")
    )

    val narrower = new TypeNarrower( constraints, trivialIdxEval )
    val recT1 = RecT( Map( "a" -> IntT, "b" -> StrT ) )
    val recT2 = RecT( Map( "c" -> StrT, "b" -> StrT ) )
    val expected1 = RecT( Map( "a" -> IntT, "b" -> StrT ) )
    val expected2 = RecT( Map( "c" -> StrT ) )
    val actual1 = narrower.narrow( recT1, 0 )
    val actual2 = narrower.narrow( recT2, 1 )

    assert( expected1 == actual1 )
    assert( expected2 == actual2 )
  }

}
