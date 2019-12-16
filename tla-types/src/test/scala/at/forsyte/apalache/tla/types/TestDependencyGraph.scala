package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.{Builder, TestingPredefs}
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestDependencyGraph extends FunSuite with TestingPredefs with BeforeAndAfter {

  import at.forsyte.apalache.tla.lir.Builder._
  import DependencyGraph.{RootNode, InternalNode}

  test( "Lone operator" ) {
    val aDecl = declOp( "A", plus( n_x, n_y ) )
    val bm = BodyMapFactory.makeFromDecl( aDecl )

    val graph = DependencyGraph.construct( bm )

    assert( graph.root == RootNode( Set( aDecl.name ) ) )
    assert( graph.nodeMap.get( aDecl.name ).contains(
      InternalNode( aDecl.name, isRecursive = false, Set.empty )
    ) )
  }

  test( "Two independent operators" ) {
    val aDecl = declOp( "A", plus( n_x, n_y ) )
    val bDecl = declOp( "B", plus( n_x, n_y ) )
    val bm = BodyMapFactory.makeFromDecls( Seq( aDecl, bDecl ) )

    val graph = DependencyGraph.construct( bm )

    assert( graph.root == RootNode( Set( aDecl.name, bDecl.name ) ) )
    assert( graph.nodeMap.get( aDecl.name ).contains(
      InternalNode( aDecl.name, isRecursive = false, Set.empty )
    ) )
    assert( graph.nodeMap.get( bDecl.name ).contains(
      InternalNode( bDecl.name, isRecursive = false, Set.empty )
    ) )
  }

  test( "Chain of length 2" ) {
    val aDecl = declOp( "A", plus( n_x, n_y ) )
    val bDecl = declOp( "B", appDecl( aDecl ) )
    val bm = BodyMapFactory.makeFromDecls( Seq( aDecl, bDecl ) )

    val graph = DependencyGraph.construct( bm )

    assert( graph.root == RootNode( Set( bDecl.name ) ) )
    assert( graph.nodeMap.get( aDecl.name ).contains(
      InternalNode( aDecl.name, isRecursive = false, Set.empty )
    ) )
    assert( graph.nodeMap.get( bDecl.name ).contains(
      InternalNode( bDecl.name, isRecursive = false, Set( aDecl.name ) )
    ) )
  }

  test( "2-to-1 dependency" ) {
    val aDecl = declOp( "A", plus( n_x, n_y ) )
    val b1Decl = declOp( "B1", appDecl( aDecl ) )
    val b2Decl = declOp( "B2", appDecl( aDecl ) )
    val bm = BodyMapFactory.makeFromDecls( Seq( aDecl, b1Decl, b2Decl ) )

    val graph = DependencyGraph.construct( bm )

    assert( graph.root == RootNode( Set( b1Decl.name, b2Decl.name ) ) )
    assert( graph.nodeMap.get( aDecl.name ).contains(
      InternalNode( aDecl.name, isRecursive = false, Set.empty )
    ) )
    assert( graph.nodeMap.get( b1Decl.name ).contains(
      InternalNode( b1Decl.name, isRecursive = false, Set( aDecl.name ) )
    ) )
    assert( graph.nodeMap.get( b2Decl.name ).contains(
      InternalNode( b2Decl.name, isRecursive = false, Set( aDecl.name ) )
    ) )
  }

  test( "1-to-2 dependency" ) {
    val a1Decl = declOp( "A1", n_x )
    val a2Decl = declOp( "A2", n_y )
    val bDecl = declOp( "B", plus( appDecl( a1Decl ), appDecl( a2Decl ) ) )
    val bm = BodyMapFactory.makeFromDecls( Seq( a1Decl, a2Decl, bDecl ) )

    val graph = DependencyGraph.construct( bm )

    assert( graph.root == RootNode( Set( bDecl.name ) ) )
    assert( graph.nodeMap.get( a1Decl.name ).contains(
      InternalNode( a1Decl.name, isRecursive = false, Set.empty )
    ) )
    assert( graph.nodeMap.get( a2Decl.name ).contains(
      InternalNode( a2Decl.name, isRecursive = false, Set.empty )
    ) )
    assert( graph.nodeMap.get( bDecl.name ).contains(
      InternalNode( bDecl.name, isRecursive = false, Set( a1Decl.name, a2Decl.name ) )
    ) )
  }

  test( "Basic recursion" ) {
    val aDecl = declOp( "A", appOp( name( "A" ) ) )
    val bm = BodyMapFactory.makeFromDecls( Seq( aDecl ) )

    val graph = DependencyGraph.construct( bm )

    assert( graph.root == RootNode( Set( aDecl.name ) ) )
    assert( graph.nodeMap.get( aDecl.name ).contains(
      InternalNode( aDecl.name, isRecursive = true, Set( aDecl.name ) )
    ) )

  }

  test( "Mutual recursion lasso" ) {
    val aDecl = declOp( "A", appOp( name( "B" ) ) )
    val bDecl = declOp( "B", appOp( name( "C" ) ) )
    val cDecl = declOp( "C", appOp( name( "B" ) ) )

    val bm = BodyMapFactory.makeFromDecls( Seq( aDecl, bDecl, cDecl ) )

    val graph = DependencyGraph.construct( bm )

    assert( graph.root == RootNode( Set( aDecl.name ) ) )
    assert( graph.nodeMap.get( aDecl.name ).contains(
      InternalNode( aDecl.name, isRecursive = false, Set( bDecl.name ) )
    ) )
    assert( graph.nodeMap.get( bDecl.name ).contains(
      InternalNode( bDecl.name, isRecursive = true, Set( cDecl.name ) )
    ) )
    assert( graph.nodeMap.get( cDecl.name ).contains(
      InternalNode( cDecl.name, isRecursive = true, Set( bDecl.name ) )
    ) )
  }

  test( "Mutual recursion loop" ) {
    val aDecl = declOp( "A", appOp( name( "B" ) ) )
    val bDecl = declOp( "B", appOp( name( "C" ) ) )
    val cDecl = declOp( "C", appOp( name( "A" ) ) )

    val bm = BodyMapFactory.makeFromDecls( Seq( aDecl, bDecl, cDecl ) )

    val graph = DependencyGraph.construct( bm )

    assert( graph.root.children.size == 1 )
    assert( graph.nodeMap.get( aDecl.name ).contains(
      InternalNode( aDecl.name, isRecursive = true, Set( bDecl.name ) )
    ) )
    assert( graph.nodeMap.get( bDecl.name ).contains(
      InternalNode( bDecl.name, isRecursive = true, Set( cDecl.name ) )
    ) )
    assert( graph.nodeMap.get( cDecl.name ).contains(
      InternalNode( cDecl.name, isRecursive = true, Set( aDecl.name ) )
    ) )
  }

}
