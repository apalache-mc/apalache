package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.imp._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.storage.{BodyMap, BodyMapFactory, SourceStoreImpl}
import at.forsyte.apalache.tla.lir.transformations.TransformationListener
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.HashMap
import scala.io.Source

/* TODO: All tests clean */

@RunWith( classOf[JUnitRunner] )
class TestTransformer extends FunSuite with TestingPredefs {
  val testFolderPath = "src/test/resources/sanitizer/"

  test( "badEx" ) {
    val text =
      """---- MODULE WrongArity ----
        |A(x) == x
        |B(Op(_,_),x) == Op(x,x)
        |C == B(A, A)
        |=======================
      """.stripMargin


    assertThrows[SanySemanticException](
      new SanyImporter(new SourceStore)
        .loadFromSource( "WrongArity", Source.fromString( text ) )
    )

    val text2 =
      """---- MODULE redef ----
        |A(x) == x
        |A(x) == x + x
        |=======================
      """.stripMargin

    assertThrows[SanySemanticException](
      new SanyImporter(new SourceStore)
        .loadFromSource( "redef", Source.fromString( text2 ) )
    )

  }

  val declEx1 = tla.declOp( "A", "x", "x" )
  val declEx2 = tla.declOp( "B", OperEx( declEx1.operator, 1 ) )
  val declEx3 = tla.declOp( "Tw", tla.appOp( n_A, n_x, n_x ), ("A", 2), "x" )
  val declEx4 = tla.declOp( "Malformed", tla.appDecl( declEx3, n_A, n_A ) )
  val declEx5 = TlaVarDecl( "x" )
  val declEx6 = TlaVarDecl( "y" )
  val declEx7 = TlaVarDecl( "z" )
  val declEx8 = tla.declOp( "Ar2", tla.plus( n_x, n_y ), "x", "y" )
  val declEx9 = tla.declOp( "Three",
    tla.appDecl( declEx3,
      declEx8.name,
      tla.appDecl( declEx1, 2 )
    )
  )

  val allDecls =
    Seq(
      declEx1,
      declEx2,
      declEx3,
      declEx4,
      declEx5,
      declEx6,
      declEx7,
      declEx8,
      declEx9
    )

  implicit val ssi : TransformationListener = new SourceStoreImpl()

  def clean( ) : Unit = {
  }

  val converter    = new Transformer()
  val allExtracted = BodyMapFactory.makeFromDecls( allDecls )

  def cleanTest( f : => Unit ) = prePostTest( f, clean )

  test( "Test getVars" ) {
    val converter = new Transformer()
    cleanTest {
      val vars = converter.getVars( declEx1, declEx2, declEx3, declEx4, declEx5, declEx6, declEx7 )
      assert( vars == Set( "x", "y", "z" ) )

      val declEx8 = tla.declOp( "foo", n_q )
      assert( converter.getVars( declEx8 ).isEmpty )
    }
  }

  test( "Test inlineAll" ) {
    val converter = new Transformer()
    cleanTest {

      assertThrows[IllegalArgumentException](
        converter.inlineAll( declEx4.body )(allExtracted, ssi)
      )
      assert( converter.inlineAll( declEx2.body )(allExtracted, ssi) == tla.int( 1 ) )
      assert( converter.inlineAll( declEx9.body )(allExtracted, ssi) == tla.plus( 2, 2 ) )

      assertThrows[IllegalArgumentException]( converter.inlineAll( tla.appOp( "A" ) )(allExtracted, ssi) )
      assert( converter.inlineAll( tla.appOp( "A", 2 ) )(allExtracted, ssi) == tla.int( 2 ) )
    }
  }

  test( "Test unchangedExplicit" ) {
    val converter = new Transformer()
    cleanTest {
      val ucEx1 = tla.unchanged( n_a )
      val ucEx2 = tla.unchangedTup( n_a, n_b )
      val ucEx3 = tla.unchanged( tla.plus( n_a, n_b ) )
      val ucEx4 =
        tla.or(
          tla.exists( n_x, n_S, tla.primeEq( n_x, 1 ) ),
          tla.forall( n_x, n_S, tla.unchanged( n_x ) )
        )

      assert( converter.unchangedExplicit( ucEx1 ) == tla.primeInSingleton( n_a, n_a ) )
      assert( converter.unchangedExplicit( ucEx2 ) ==
        tla.and( tla.primeInSingleton( n_a, n_a ), tla.primeInSingleton( n_b, n_b ) )
      )
      assert( converter.unchangedExplicit( ucEx3 ) == ucEx3 )
      assert( converter.unchangedExplicit( ucEx4 ) ==
        tla.or(
          tla.exists( n_x, n_S, tla.primeEq( n_x, 1 ) ),
          tla.forall( n_x, n_S, converter.unchangedExplicit( tla.unchanged( n_x ) ) )
        )
      )

    }
  }

  test( "Test NullEx" ) {
    val converter = new Transformer()
    cleanTest {

      assert( converter(NullEx)(BodyMapFactory.newMap, ssi).isEmpty )
    }
  }

  test( "Test sanitize" ) {
    val converter = new Transformer()
    cleanTest {

      assert( converter.sanitize( declEx1.body )(allExtracted, ssi) == declEx1.body )

      assertThrows[IllegalArgumentException]( converter.sanitize( declEx4.body )(allExtracted, ssi) )
      assert(
        converter.sanitize( declEx2.body )(allExtracted, ssi) ==
          converter.inlineAll( declEx2.body )(allExtracted, ssi) )
      assert(
        converter.sanitize( declEx9.body )(allExtracted, ssi) ==
          converter.inlineAll( declEx9.body )(allExtracted, ssi) )

      assertThrows[IllegalArgumentException]( converter.sanitize( tla.appOp( "A" ) )(allExtracted, ssi) )
      assert(
        converter.sanitize( tla.appOp( "A", 2 ) )(allExtracted, ssi)
        == converter.inlineAll( tla.appOp( "A", 2 ) )(allExtracted, ssi) )

      assert(
        converter.sanitize( tla.primeEq( n_x, n_y ) )(allExtracted, ssi)
          == tla.primeInSingleton( n_x, n_y ) )
      assert(
        converter.sanitize( tla.enumSet( tla.primeEq( n_x, n_y ) ) )(allExtracted, ssi)
          == tla.enumSet( tla.primeInSingleton( n_x, n_y ) ) )
    }
  }

  test( "Test on files" ) {
    val converter = new Transformer()
    cleanTest {
      val fname1 = "test1.tla"
      val declarations1 = declarationsFromFile(testFolderPath + fname1)

      val bm = BodyMapFactory.makeFromDecls( declarations1 )

      assert(
        bm.get( "Next" ).map( _._2 ).contains(
          tla.and(
            tla.primeEq( n_a, 1 ),
            tla.primeEq( n_b, tla.eql( n_e, n_f ) ),
            tla.in( tla.prime( n_c ), tla.enumSet( n_e, n_f, n_g ) ),
            tla.primeEq( n_d, 4 ),
            tla.unchanged( tla.tuple( n_x, n_y ) ),
            tla.unchanged( n_z )
          )
        )
      )

      assert(
        bm.get( "Init" ).map( _._2 ).contains(
          tla.eql( n_a, 0 )
        )
      )

      assert(
        bm.get( "Spec" ).map( _._2 ).contains(
          tla.box(
            tla.stutt(
              tla.appDecl( declarations1.find( _.name == "Next" ).get.asInstanceOf[TlaOperDecl] ),
              tla.tuple( n_a, n_b )
            )
          )
        )
      )

    }

    cleanTest {
      val fileName = "test2.tla"
      val declarations = declarationsFromFile(testFolderPath + fileName)

      val bm = BodyMapFactory.makeFromDecls( declarations )

      val nextBody = findBodyOf( "Next", declarations:_*)

      assert( nextBody != NullEx )

      val after = converter.sanitize( nextBody )(bm, ssi)

      val expected =
        tla.and(
          tla.or(
            tla.and(
              tla.primeInSingleton( n_a, tla.prime( n_b ) ),
              tla.primeInSingleton( n_b, tla.prime( n_a ) )
            ),
            tla.primeInSingleton( n_b, 2 )
          ),
          tla.primeInSingleton( n_a, 1 )
        )

      assert(after == expected)
    }

    cleanTest {
      val fileName = "test3.tla"
      val declarations = declarationsFromFile(testFolderPath + fileName)

      val bm = BodyMapFactory.makeFromDecls( declarations )

      val nextBody = findBodyOf( "Next", declarations:_*)

      assert( nextBody != NullEx )

      val after = converter.sanitize( nextBody )(bm, ssi)

      val expected =
        tla.and(
          tla.or(
            tla.and(
              tla.primeInSingleton( n_a, tla.prime( n_b ) ),
              tla.primeInSingleton( n_b, tla.prime( n_a ) )
            ),
            tla.exists(
              n_p,
              tla.enumSet( 1, 2 ),
              tla.primeInSingleton( n_b, n_p )
            )
          ),
          tla.primeInSingleton( n_a, 1 ),
          tla.forall(
            n_q,
            tla.enumSet(1),
            tla.primeInSingleton( n_a, n_q )
          )
        )

      assert( after == expected )
    }

  }

}
