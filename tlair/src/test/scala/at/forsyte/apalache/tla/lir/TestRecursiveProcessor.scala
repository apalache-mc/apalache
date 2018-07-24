package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.convenience._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.collection.mutable.{Set => MSet}
import at.forsyte.apalache.tla.lir.plugins.Identifier

@RunWith( classOf[JUnitRunner] )
class TestRecursiveProcessor extends FunSuite with TestingPredefs {
  test( "Default functions" ) {
    /** Nat. term. */
    def nt[T] = RecursiveProcessor.DefaultFunctions.naturalTermination[T]

    assert( !nt( 1 ) )
    assert( !nt( Seq.empty[Set[Set[OperEx]]] ) )
    assert( !nt( "a string" ) )
    assert( !nt( Set( n_x, x_in_S ) ) )

    /** Noop */
    def no[T] = RecursiveProcessor.DefaultFunctions.noOp[T]

    assert( no( 1 ) === () )
    assert( no( Seq.empty[Set[Set[OperEx]]] ) === () )
    assert( no( "a string" ) === () )
    assert( no( Set( n_x, x_in_S ) ) === () )

    /** ChildCollect */
    def setUnion[T1, T2] : (T1, Traversable[Set[T2]]) => Set[T2] =
      RecursiveProcessor.DefaultFunctions.childCollect[T1, Set[T2]]( Set.empty[T2], _ ++ _ )

    val set1 = Set( 1, 2, 3 )
    val set2 = Set( 3, 4, 5 )

    val lst = List( set1, set2 )

    assert( setUnion( 1, lst ) == set1 ++ set2 )
    assert( setUnion( "axasd", lst ) == set1 ++ set2 )
    assert( setUnion( None, Seq( set1 ) ) == set1 )
    assert( setUnion( None, Seq() ).isEmpty )

    def sum[T1] : (T1, Traversable[Int]) => Int =
      RecursiveProcessor.DefaultFunctions.childCollect[T1, Int]( 0, _ + _ )

    val lst2 = List( 2, 4, 6, 8 )
    var lstsum = 0
    lst2.foreach( x => lstsum += x )


    assert( sum( 1, lst2 ) == lstsum )
    assert( sum( "axasd", lst2 ) == lstsum )
    assert( sum( None, Seq( 1 ) ) == 1 )
    assert( sum( None, Seq() ) == 0 )

    /** SubtypeHasC */

    abstract class A
    sealed class B extends A
    sealed class C extends A

    def cls : A => Boolean = RecursiveProcessor.DefaultFunctions.subtypeHasChildren[A, B]

    assert( cls( new B ) && !cls( new C ) )

    /** SubtypeGetChildren */
    val deflist = List( new B, new B, new C, new B, new C )

    def children : B => List[A] = _ => deflist

    def getc : A => Traversable[A] =
      RecursiveProcessor.DefaultFunctions.subtypeGetChildren[A, B]( children )

    assert( getc( new B ) === deflist )
    assert( getc( new C ).isEmpty )

    /** IgnoreC */
    type T = List[Set[Int]]

    def lstfun( v : T ) : Int = v.map( _.min ).fold( 0 ) { ( a, b ) => a * a + b * b }

    def fn : (T, Traversable[Int]) => Int =
      RecursiveProcessor.DefaultFunctions.ignoreChildren[T, Int]( lstfun )

    val lst3 = List( 1, 2, 3 )
    val setLst3 = List( Set( 1, 2 ), Set( 2, 3 ), Set( 3, 4 ) )

    assert( fn( setLst3, lst3 ) === 34 )
    assert( fn( setLst3, List.empty[Int] ) === fn( setLst3, lst3 ) )
  }

  ignore( "Proper termination" ) {

    def terminationTest( p_ex : TlaEx ) : Boolean = p_ex match {
      case NameEx( n ) => true
      case _ => false
    }

    def terminalFun( p_ex : TlaEx ) : Unit = p_ex match {
      case NameEx( n ) => println( n )
      case _ => ()
    }

    def nonterminalFun( p_ex : TlaEx ) : Unit = println( p_ex + " is not a NameEx" )

    def unification( p_ex : TlaEx, p_children : Traversable[Unit] ) : Unit = ()

    val ex = tla.primeInSingleton( n_x, n_S )

    val fun = RecursiveProcessor.computeFromTlaEx( terminationTest, terminalFun, nonterminalFun, unification )

    fun( ex )

    fun( trueEx )
  }

  test( "Correct traversal" ) {
    var idCollector : MSet[UID] = MSet.empty

    def collect( p_ex : TlaEx ) : Unit = idCollector.add( p_ex.ID )

    val ex1 = tla.primeInSingleton( n_x, n_S )
    val ex2 = tla.ite( tla.eql( 0, 1 ), n_p, n_q )
    val ex3 = tla.exists( n_x, n_T, tla.and( ex1, ex2 ) )

    Identifier.identify( ex3 )

    val fun = RecursiveProcessor.traverseEntireTlaEx( collect )

    fun( ex3 )

    assert( Set( ex1.ID, ex2.ID, ex3.ID ).subsetOf( idCollector ) )

  }

  test( "Fixpoint" ) {
    val recLimit = 300

    def f( x : Int ) : Int = x + 1

    assert( RecursiveProcessor.computeFixpoint( f )( 0 )( recLimit ).isEmpty )

    def g( x : Double ) : Double = math.cos(x)

    val eps = 0.00001

    def d( x : Double, y : Double ) : Double = ( x - y ).abs

    val fp = RecursiveProcessor.computeFixpoint(
      g,
      RecursiveProcessor.DefaultFunctions.epsEquality( eps, d )
    )( -1 )( recLimit )

    assert(fp.nonEmpty)

  }

}