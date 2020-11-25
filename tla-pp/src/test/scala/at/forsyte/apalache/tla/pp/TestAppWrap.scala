package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaOper}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestAppWrap extends FunSuite with BeforeAndAfterEach with TestingPredefs {

  private var wrapper = new AppWrap( new UniqueNameGenerator, TrackerWithListeners() )

  override def beforeEach( ) : Unit = {
    wrapper = new AppWrap( new UniqueNameGenerator, TrackerWithListeners() )
  }

  test( "No app" ) {
    val exs = List(
      tla.plus( 1, 2 ),
      tla.tuple( n_x, n_y, n_z ),
      tla.exists( n_x, n_S, tla.gt( n_x, n_f ) )
    )

    val tr = wrapper.wrap( Set.empty )
    val newExs = exs map tr
    assert( exs == newExs )
  }

  test( "Single App" ) {
    val ex = tla.appOp( n_A, n_x, n_y )

    val tr1 = wrapper.wrap( Set.empty )
    val tr2 = wrapper.wrap( Set( "A" ) )
    val newEx1 = tr1( ex )
    val newEx2 = tr2( ex )

    val assertCond1 = newEx1 == ex
    val assertCond2 = newEx2 match {
      case LetInEx(
      OperEx( TlaOper.apply, NameEx( someName ) ),
      TlaOperDecl( declName, Nil, defEx ) ) if declName == someName =>
        defEx == ex
      case _ => false
    }

    assert( assertCond1 && assertCond2 )
  }


  test( "Mixed" ) {
    val ex1 = tla.appOp( n_A, n_x, n_y )
    val ex2 = tla.appOp( n_B, n_x, n_y )
    val ex = tla.plus( ex1, ex2 )

    val tr = wrapper.wrap( Set( "A" ) )
    val newEx = tr( ex )

    val assertCond = newEx match {
      case OperEx( TlaArithOper.plus, exA, exB ) =>
        val condA = exA match {
          case LetInEx(
          OperEx( TlaOper.apply, NameEx( someName ) ),
          TlaOperDecl( declName, Nil, defEx ) ) if declName == someName =>
            defEx == ex1
          case _ => false
        }
        val condB = exB == ex2
        condA && condB
      case _ => false
    }

    assert( assertCond )
  }

}

