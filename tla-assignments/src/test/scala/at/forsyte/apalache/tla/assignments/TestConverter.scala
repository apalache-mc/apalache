package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import convenience._
import Converter._
import at.forsyte.apalache.tla.imp._
import at.forsyte.apalache.tla.lir.db.DB
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.io.Source

/* TODO: All tests clean */

@RunWith( classOf[JUnitRunner] )
class TestConverter extends FunSuite with TestingPredefs {
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
      new SanyImporter().loadFromSource( "WrongArity", Source.fromString( text ) )
    )

    val text2 =
      """---- MODULE redef ----
        |A(x) == x
        |A(x) == x + x
        |=======================
      """.stripMargin

    assertThrows[SanySemanticException](
      new SanyImporter().loadFromSource( "redef", Source.fromString( text2 ) )
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

  implicit val bDB : BodyDB = new BodyDB()

  def clean( ) : Unit = bDB.clear()

  def cleanTest( f : => Unit ) = prePostTest( f, clean )

  test( "Test extract" ) {


    extract( declEx1, declEx2 )

    assert( !( bDB == Map( declEx2.name -> (declEx2.formalParams, declEx2.body) ) ) )
    assert(
      bDB == Map(
        declEx1.name -> (declEx1.formalParams, declEx1.body),
        declEx2.name -> (declEx2.formalParams, declEx2.body)
      )
    )

    extract( declEx5, declEx6, declEx7 )

    assert( !( bDB == Map( declEx2.name -> (declEx2.formalParams, declEx2.body) ) ) )
    assert(
      bDB == Map(
        declEx1.name -> (declEx1.formalParams, declEx1.body),
        declEx2.name -> (declEx2.formalParams, declEx2.body)
      )
    )


    extract( declEx1, declEx2, declEx3, declEx4 )

    assert(
      bDB == Map(
        declEx1.name -> (declEx1.formalParams, declEx1.body),
        declEx2.name -> (declEx2.formalParams, declEx2.body),
        declEx3.name -> (declEx3.formalParams, declEx3.body),
        declEx4.name -> (declEx4.formalParams, declEx4.body)
      )
    )
  }

  test( "Test getVars" ) {
    val vars = getVars( declEx1, declEx2, declEx3, declEx4, declEx5, declEx6, declEx7 )
    assert( vars == Set( "x", "y", "z" ) )

    val declEx8 = tla.declOp( "foo", n_q )
    assert( getVars( declEx8 ).isEmpty )

  }

  test( "Test inlineAll" ) {
    extract( declEx8, declEx9 )

    assertThrows[IllegalArgumentException]( inlineAll( declEx4.body ) )
    assert( inlineAll( declEx2.body ) == tla.int( 1 ) )
    assert( inlineAll( declEx9.body ) == tla.plus( 2, 2 ) )

    assertThrows[IllegalArgumentException]( inlineAll( tla.appOp( "A" ) ) )
    assert( inlineAll( tla.appOp( "A", 2 ) ) == tla.int( 2 ) )
  }

  test( "Test sanitize" ) {
    assert( sanitize( declEx1.body ) == declEx1.body )

    assertThrows[IllegalArgumentException]( sanitize( declEx4.body ) )
    assert( sanitize( declEx2.body ) == inlineAll( declEx2.body ) )
    assert( sanitize( declEx9.body ) == inlineAll( declEx9.body ) )

    assertThrows[IllegalArgumentException]( sanitize( tla.appOp( "A" ) ) )
    assert( sanitize( tla.appOp( "A", 2 ) ) == inlineAll( tla.appOp( "A", 2 ) ) )

    assert( sanitize( tla.eql( 0, 1 ) ) == tla.in( 0, tla.enumSet( 1 ) ) )
    assert( sanitize( tla.enumSet( tla.eql( 0, 1 ) ) ) == tla.enumSet( tla.in( 0, tla.enumSet( 1 ) ) ) )
  }

  test( "Test unchangedExplicit" ){
    cleanTest {
      val ucEx1 = tla.unchanged( n_a )
      val ucEx2 = tla.unchangedTup( n_a, n_b )
      val ucEx3 = tla.unchanged( tla.plus( n_a, n_b ) )
      val ucEx4 = tla.unchanged( n_a )

//      assert( unchangedExplicit( ucEx1 ) == tla.and(  ) )


    }
  }

  test( "Test on files" ) {

    cleanTest {
      val fname1 = "test1.tla"
      val declarations1 = declarationsFromFile( testFolderPath + fname1 )

      extract( declarations1 : _* )

      assert(
        bDB.body( "Next" ).contains(
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
        bDB.body( "Init" ).contains(
          tla.eql( n_a, 0 )
        )
      )

      assert(
        bDB.body( "Spec" ).contains(
          tla.box(
            tla.stutt(
              tla.appDecl( declarations1.find( _.name == "Next" ).get.asInstanceOf[TlaOperDecl] ),
              tla.tuple( n_a, n_b )
            )
          )
        )
      )
      //
      //
      //
      //      assert(
      //        bDB == Map(
      //          "Next" -> (List(), tla.and(
      //            tla.primeEq( n_a, 1 ),
      //            tla.primeEq( n_b, tla.eql( n_e, n_f ) ),
      //            tla.in( tla.prime( n_c ), tla.enumSet( n_e, n_f, n_g ) ),
      //            tla.primeEq( n_d, 4 ),
      //            tla.unchanged( tla.tuple( n_x, n_y ) ),
      //            tla.unchanged( n_z )
      //          )),
      //          "Init" -> (List(), tla.eql( n_a, 0 )),
      //          "Spec" -> (List(), tla.box( tla.stutt( "Next", tla.tuple( n_a, n_b ) ) ))
      //        )
      //      )

      //      bDB.print()


    }


  }

  //  test("Check sanitization") {
  //    val fileName = "assignmentTest2.tla"
  //    val extracted = sanitizer(testFolderPath + fileName)
  //    assert(extracted.isDefined)
  //    val after = extracted.get
  ////    println( "%s \n -> \n %s".format( before, after ) )
  //
  //    val ap = bd.prime( "a" )
  //
  //    val expected =
  //      bd.and(
  //        bd.or(
  //          bd.and(
  //            bd.in( bd.prime( "a" ), bd.enumSet( bd.prime( "b" ) ) ),
  //            bd.in( bd.prime( "b" ), bd.enumSet( bd.prime( "a" ) ) )
  ////            bd.primeEq( "a", "b" ),
  ////            bd.primeEq( "b", "a" )
  //          ),
  //          bd.in( bd.prime( "b" ), bd.enumSet( bd.bigInt( 2 ) ) )
  ////          bd.primeEq( "b", 2)
  //        ),
  //        bd.in( bd.prime( "a" ), bd.enumSet( bd.bigInt( 1 ) ) )
  ////        bd.primeEq( "a", 1 )
  //      )
  //
  //    assert(after == expected)
  //  }
  //
  //  test( "Check quantifiers" ){
  //
  //    val fileName = "assignmentTestQuantifiers.tla"
  //    val extracted = sanitizer(testFolderPath + fileName)
  //    assert(extracted.isDefined)
  //    val after = extracted.get
  //    //    println( "%s \n -> \n %s".format( before, after ) )
  //
  //    val bd = Builder
  //
  //    val expected =
  //      bd.and(
  //        bd.or(
  //          bd.and(
  //            bd.in( bd.prime( "a" ), bd.enumSet( bd.prime( "b" ) ) ),
  //            bd.in( bd.prime( "b" ), bd.enumSet( bd.prime( "a" ) ) )
  //          ),
  //          bd.exists(
  //            bd.name("p"),
  //            bd.enumSet( bd.bigInt( 1 ), bd.bigInt( 2 ) ),
  //            bd.in( bd.prime( "b" ), bd.enumSet( bd.name( "p" ) ) )
  //          )
  //        ),
  //        bd.in( bd.prime( "a" ), bd.enumSet( bd.bigInt( 1 ) ) ),
  //        bd.forall(
  //          bd.name( "q" ),
  //          bd.enumSet( bd.bigInt( 1 )  ),
  //          bd.in( bd.prime( "a" ), bd.enumSet( bd.name( "q" ) ) )
  //        )
  //
  //      )
  //
  //    assert(after == expected)
  //
  //    val p_vars : Set[NameEx] = Set( bd.name( "a" ), bd.name( "b" ) )
  //
  //    val solution = assignmentSolver.getOrder( p_vars , after.asInstanceOf[OperEx] )
  //
  //    assert( solution.isDefined )
  //
  ////    solution.get.foreach( x => println( UniqueDB.apply( x ).get ) )
  //
  //  }
  //
  //  test("Test markTree"){
  //    UniqueDB.clear()
  //
  //    val fileName = "assignmentTestSymbNexts.tla"
  //    val extracted = sanitizer(testFolderPath + fileName).get.asInstanceOf[OperEx]
  //    val p_vars : Set[NameEx] = Set( bd.name( "a" ), bd.name( "b" ) )
  //
  ////    println( extracted.toNiceString() )
  //
  //    val solution = assignmentSolver.getOrder( p_vars , extracted ).get
  //
  //    val solutionTrim = Seq(solution.head, solution.tail.head)
  //
  //    val manualAsgns = Set( UID( 20 ), UID( 70 ) )
  //
  //    val nexts = assignmentSolver.getSymbNexts( extracted, solution )
  //
  //    nexts.foreach( pa => println( "%s -> %s".format(
  //      pa._1.map( UniqueDB( _ ).get ),
  //      pa._2 )
  //    )
  //    )
  //
  //
  //  }

}
