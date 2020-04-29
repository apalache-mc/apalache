//package at.forsyte.apalache.tla.types
//
//import at.forsyte.apalache.tla.lir.TestingPredefs
//import org.junit.runner.RunWith
//import org.scalatest.{BeforeAndAfter, FunSuite}
//import org.scalatest.junit.JUnitRunner
//
//@RunWith( classOf[JUnitRunner] )
//class TestUnification extends FunSuite with TestingPredefs with BeforeAndAfter {
//  val unifier = new TypeUnifier
//
//  val tvg = new TypeVarGenerator
//
//  test( "Incompatible" ){
//    val t1 = IntT
//    val t2 = StrT
//
//    assert( unifier.unify( t1, t2 ).isEmpty )
//
//  }
//
//  test( "_ + TypeVar" ){
//    val t1 = IntT
//    val t2 = SetT( IntT )
//    val t3 = OperT( TupT( IntT, FunT( IntT, IntT ) ), IntT )
//    val t = tvg.getUnique
//    val ts = List(t1,t2,t3)
//
//    ts foreach { ti =>
//      assert( unifier.unify( ti, t ).contains( ti ) )
//    }
//  }
//
//  test( "TypeVar at lower level" ){
//    val t1 = SetT( IntT )
//    val t2 = SetT( tvg.getUnique )
//
//    assert( unifier.unify( t1, t2 ).contains( t1 ) )
//  }
//
//  test( "Ambiguous resolution" ){
//    val t1 = AmbiguousType( IntT, StrT )
//    val t2 = IntT
//
//    assert( unifier.unify( t1, t2 ).contains( t2 ) )
//  }
//
//
//}
