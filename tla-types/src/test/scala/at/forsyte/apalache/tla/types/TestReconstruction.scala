package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.types.Names.{dtName, intTName, tupTName}
import at.forsyte.apalache.tla.types.smt.TypeReconstructor
import com.microsoft.z3.{Context, DatatypeSort, Expr, Sort}
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestReconstruction extends FunSuite with TestingPredefs with BeforeAndAfter {
  var converter = new StrIdConverter
  var ctx       = new Context

  before {
    converter = new StrIdConverter
    ctx = new Context
  }

  test( "Test tupT" ) {
    val intC = ctx.mkConstructor( intTName, s"is$intTName", null, null, null )
    val tupC = ctx.mkConstructor( tupTName, s"is$tupTName", Array( "i" ), Array[Sort]( ctx.getIntSort ), null )
    val tlaTypeDTS : DatatypeSort = ctx.mkDatatypeSort( dtName, Array( intC, tupC ) )
    val intEx = ctx.mkApp( intC.ConstructorDecl )

    def idxFun( i : Int, j : Int ) : Option[Expr] =
      (i, j) match {
        case (1, 0) | (1, 1) => Some( intEx )
        case _ => None
      }

    def fieldFun( i : Int, j : Int ) : Option[Expr] = None

    def sizeFun( i : Int ) : Int = 2

    val reconstructor = new TypeReconstructor( idxFun, fieldFun, sizeFun, converter )

    val ex1 = ctx.mkApp( tupC.ConstructorDecl, ctx.mkInt( 1 ) )
    val type1 = reconstructor( ex1 )
    assert( type1 == TupT( IntT, IntT ) )

    val ex2 = ctx.mkApp( tupC.ConstructorDecl, ctx.mkInt( 2 ) )
    val type2 = reconstructor( ex2 )
    assert( type2 match {
      case TupT( TypeVar( i ), TypeVar( j ) ) => i != j
      case _ => false
    } )
  }
}
