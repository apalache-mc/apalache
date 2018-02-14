package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.imp._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.plugins.UniqueDB
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import at.forsyte.apalache.tla.lir.{Builder => bd}

/**
  * Tests for the assignment solver
  */
@RunWith(classOf[JUnitRunner])
class TestAssignments extends FunSuite with TestingPredefs {
  val testFolderPath = "src/test/resources/assignmentSolver/"

//  test("Check dependency set computation") {
//
//    val vars : Set[NameEx] = Range(0,8).map( x => NameEx( x.toString ) ).toSet
//
//    def makeLeafFull( lhs: String, rhs: String, primed : Boolean ) : OperEx = {
//      return OperEx(
//        TlaSetOper.in,
//        OperEx(
//          TlaActionOper.prime,
//          NameEx( lhs )
//        ),
//        if (primed)
//          OperEx(
//            TlaActionOper.prime,
//            NameEx( rhs )
//          )
//        else NameEx(rhs)
//      )
//    }
//    def makeLeaf( lhs: String ) : OperEx = makeLeafFull( lhs, lhs , false )
//    def makeLeafBranches( oper: TlaOper, names: String* ) : OperEx = {
//      return OperEx( oper, names.map( makeLeaf ):_* )
//    }
//    def makeLeafBranchesBoth( oper: TlaOper, names: (String,String,Boolean)* ) : OperEx = {
//      return OperEx( oper, names.map( pa => makeLeafFull( pa._1, pa._2, pa._3 ) ):_* )
//    }
//
//    val phi1 = makeLeafBranches( TlaBoolOper.and, "0", "1" )
//    val phi2 = OperEx(  TlaBoolOper.and,
//                        makeLeafBranches( TlaBoolOper.or, "2", "3" ),
//                        makeLeafBranches( TlaBoolOper.or, "4", "5" )
//    )
//    val phi3 =
//      OperEx(
//        TlaBoolOper.or,
//        phi1,
//        phi2
//    )
//    val phi4=
//      OperEx(
//        TlaBoolOper.and,
//        phi3,
//        makeLeafBranches( TlaBoolOper.and, "6", "7" )
//      )
//
//    Identifier.identify( phi4 )
//
//    val importer = new SanyImporter()
//
//    val name1 = "assignmentTest1"
//
//    val src1 = Source.fromFile(testFolderPath + name1 + ".tla")
//
//    val (rootName1, modules1) = importer.loadFromSource(name1, Source.fromFile(testFolderPath + name1 + ".tla") )
//    val phi_ =
//      modules1(rootName1).declarations.find { _.name == "Next"} match {
//        case Some(d: TlaOperDecl) =>
//          d.body match {
//            case OperEx( op, agrs@_* ) => d.body.asInstanceOf[OperEx]
//            case _ => NullEx
//          }
//
//        case _ =>
//          NullEx
//      }
//
//    val vars1 = (
//      for {decl <- modules1(rootName1).declarations if decl.isInstanceOf[TlaVarDecl]}
//        yield NameEx(decl.name)
//      ).toSet
//
//    assert( phi_ != NullEx )
//    val phi = phi_.asInstanceOf[OperEx]
//
//    Identifier.identify( phi )
//
//    val fname = testFolderPath + name1 + ".smt2"
//
//    val ret =  assignmentSolver.getOrder(vars1, phi, fname )
//
//    assert( ret.nonEmpty )
//
////    ret.get.foreach( pa => println( "%s -> %s".format( pa._1.id, pa._2 ) ) )
//
//  }
//
//
//
//  test( "Test makeSpec" ){
//    val testDir =  testFolderPath + "sanitizer/"
//  }

  //    test( "Test markTree" ) {
  //      UniqueDB.clear()
  //
  //      val fileName = "assignmentTestSymbNexts.tla"
  //      val extracted = sanitizer( testFolderPath + fileName ).get.asInstanceOf[OperEx]
  //      val p_vars : Set[NameEx] = Set( bd.name( "a" ), bd.name( "b" ) )
  //
  //      //    println( extracted.toNiceString() )
  //
  //      val solution = assignmentSolver.getOrder( p_vars, extracted ).get
  //
  //      val solutionTrim = Seq( solution.head, solution.tail.head )
  //
  //      val manualAsgns = Set( UID( 20 ), UID( 70 ) )
  //
  //      val nexts = assignmentSolver.getSymbNexts( extracted, solution )
  //
  //      nexts.foreach( pa => println( "%s -> %s".format(
  //        pa._1.map( UniqueDB( _ ).get ),
  //        pa._2 )
  //      )
  //      )
  //
  //
  //
  //        }

  //    }

  ignore( "Test on real files" ) {
    val file = "EWD840.tla"
    UniqueDB.clear() // Igor: why do you need UniqueDB here?

    val decls = declarationsFromFile(testFolderPath + file)
    val converter = new Converter()
    converter.extract( decls:_* )

    val nextBody = findBodyOf( "Next", decls:_* )

    val vars = converter.getVars( decls:_*)
    val cleaned = converter.sanitize( nextBody )

    val order = assignmentSolver.getStrategy( vars, cleaned )

    assert( order.isDefined )

//    println( order.get.size )
//      order.get.foreach( x => println( UniqueDB( x ).get ) )

    val symbNexts = assignmentSolver.getSymbNexts( cleaned, order.get )

//    assert( symbNexts.forall( x =>  true ) )

//    printsep()
//    println( symbNexts.size )
//    symbNexts.foreach( x =>  println( "%s : %s".format( x._1.map( p => (UniqueDB(p).get, p ) ) , x._2 ) ) )

  }

  /*
  TODO: fix IF-THEN-ELSE

  test( "Test Prisoners" ){
    val file = "PrisonersNoCard.tla"

    UniqueDB.clear()
    Converter.clear()

    val decls = declarationsFromFile(testFolderPath + file)
    val vars = Converter.getVars( decls:_*)
    val nextBody = findBodyOf( "Next", decls:_* )

    assert( ! nextBody.isNull )

    val cleaned = Converter( nextBody, decls:_* )
    assert( nextBody.ID.valid )

    assert( cleaned.isDefined )
    assert( cleaned.get.ID.valid )

    val strat = assignmentSolver.getStrategy( vars, cleaned.get )

    assert( strat.isDefined )

    //    println( order.get.size )
    //      order.get.foreach( x => println( UniqueDB( x ).get ) )

    val symbNexts = assignmentSolver.getSymbNexts( cleaned.get, strat.get )
  }
  */

  ignore( "Test dangerous cases" ){

    val file = "negation.tla"

    UniqueDB.clear() // Igor: why do you need UniqueDB here?
    val converter = new Converter()


    val decls = declarationsFromFile(testFolderPath + file)
    val vars = converter.getVars( decls:_*)
    val nextBody = findBodyOf( "Next", decls:_* )

    assert( ! nextBody.isNull )

    val cleaned = converter( nextBody, decls:_* )
    assert( nextBody.ID.valid )

    assert( cleaned.isDefined )
    assert( cleaned.get.ID.valid )

    val strat = assignmentSolver.getStrategy( vars, cleaned.get )

    assert( strat.isDefined )

    //    println( order.get.size )
    //      order.get.foreach( x => println( UniqueDB( x ).get ) )

    val symbNexts = assignmentSolver.getSymbNexts( cleaned.get, strat.get )


  }

  ignore( "Test bound variable name clashes"){
    /**
      *
      * Bug: The operator subsitution can clash with e.g. quantified variables of the same name.
      * Possible solution: preprocessing step where all FormalParameter and all bound vars are uniquely named
      *
      * */

    UniqueDB.clear()

    val sameName = n_x
    val bodyA = sameName
    val declA = TlaOperDecl( "A", List( SimpleFormalParam( sameName.name ) ), bodyA )

    val args = bd.enumSet( sameName, sameName )
    val bodyNext = bd.exists( sameName, NullEx, bd.appDecl( declA, args ) )
    val declNext = TlaOperDecl( "Next", List(), bodyNext )

    val converter = new Converter()

//    assert( converter( bodyNext, declA ) contains bd.exists(sameName, NullEx, args) )
//    assertThrows[StackOverflowError]( converter( bodyNext, declA ) )

    val newDecls = OperatorHandler.uniqueVarRename( Seq( declA, declNext ) )
    val newBodyNext = findBodyOf( "Next", newDecls:_* )

    val ret = converter( bodyNext, newDecls:_* )
    assert( ret contains bd.exists( sameName, NullEx, args ) )

  }

  def testFromFile( p_file: String, p_next:String = "Next" ) : Seq[assignmentSolver.SymbNext] = {
    UniqueDB.clear()
    val converter = new Converter()


    val declsOld = declarationsFromFile(testFolderPath + p_file)
    val declsRenamed = OperatorHandler.uniqueVarRename( declsOld )
    val decls = declsRenamed.map(
      decl => decl match {
        case TlaOperDecl( name, params, body ) =>
          TlaOperDecl( name, params, converter.explicitLetIn( body ) )
        case _ => decl
      }
    )

    val vars = converter.getVars( decls:_*)
    val nextBody = findBodyOf( p_next, decls:_* )

    assert( ! nextBody.isNull )

    val cleaned = converter( nextBody, decls:_* )
    assert( nextBody.ID.valid )

    assert( cleaned.isDefined )
    assert( cleaned.get.ID.valid )

    val strat = assignmentSolver.getStrategy( vars, cleaned.get )

    assert( strat.isDefined )

//    Seq()
    //    println( order.get.size )
    //      order.get.foreach( x => println( UniqueDB( x ).get ) )

    assignmentSolver.getSymbNexts( cleaned.get, strat.get )
  }

  test( "Test Paxos (simplified)" ){

    val symbNexts = testFromFile( "Paxos.tla" )
    println( symbNexts.size )

  }

  ignore("Test ITE_CASE") {


    val symbNexts = testFromFile( "ITE_CASE.tla" )

  }

  test("Test EWD840") {


    val symbNexts = testFromFile( "EWD840.tla" )
    println( symbNexts.size )
  }

  test( "AST" ){

//    testFromFile( "ast.tla" )
  }

}
