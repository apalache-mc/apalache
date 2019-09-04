package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.imp.declarationsFromFile
import at.forsyte.apalache.tla.lir.process.Renaming
import at.forsyte.apalache.tla.lir.storage.{BodyMapFactory, ChangeListener}
import at.forsyte.apalache.tla.lir.transformations.TlaExTransformation
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.{NullEx, TestingPredefs, TlaDecl, TlaEx, TlaModule, TlaOperDecl, TlaVarDecl, UID, Builder => bd}
import at.forsyte.apalache.tla.pp.Desugarer
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbTransPass extends FunSuite with TestingPredefs with TypeAliases {
  val testFolderPath = "src/test/resources/assignmentSolver/"

  def testFromNext( p_next : TlaEx ) : Seq[SymbTrans] = {
    testFromDecls( Seq( TlaOperDecl( "Next", List(), p_next ) ) )
  }

  def testFromDecls( p_decls : Seq[TlaDecl], p_next : String = "Next"   ) : Seq[SymbTrans]  = {
    val fakeModule = new TlaModule("test", Seq.empty, p_decls)
    val srcDB = new ChangeListener

    val tracker = TrackerWithListeners( srcDB )
    val afterDesugarer = ModuleByExTransformer(Desugarer(tracker)) (fakeModule)
    val renaming = new Renaming( tracker )
    val uniqueVarDecls =
      new TlaModule(
        afterDesugarer.name,
        afterDesugarer.imports,
        afterDesugarer.declarations map {
          renaming.apply
        }
      )

    val bodyMap = BodyMapFactory.makeFromDecls( uniqueVarDecls.operDeclarations )
    val inlined = ModuleByExTransformer( Inline( bodyMap, tracker ) )( uniqueVarDecls )
    val explLetIn = ModuleByExTransformer( ExplicitLetIn( tracker, keepNullary = false ) )( inlined )
    val eac = ModuleByExTransformer( EqualityAsContainment( tracker ) )( explLetIn )
    val explUC = ModuleByExTransformer( ExplicitUnchanged( tracker ) )( eac )
    val preprocessed = ModuleByExTransformer(  SimplifyRecordAccess( tracker ) )( explUC )

    new SymbolicTransitionExtractor(tracker)(preprocessed.declarations, p_next)
  }

  def testFromFile( p_file : String, p_next : String = "Next" ) : Seq[SymbTrans] = {

    val decls = declarationsFromFile(testFolderPath + p_file)

    val ret = testFromDecls( decls, p_next )

//    val saveWriter = new PrintWriter( new File( testFolderPath + "SymbNexts" + p_file ) )

//    ret.foreach( x => saveWriter.println( "%s : \n %s\n".format( x._1.map( UniqueDB.get ) , x._2 ) ) )

//    saveWriter.close()

    ret
  }

  test( "Test labelsAt" ){
    val gen = new SymbTransGenerator( TrackerWithListeners() )

    assert( gen.helperFunctions.labelsAt(NullEx, Map.empty[UID, Set[Set[UID]]]).isEmpty )
  }

  test( "Test Complete Spec return + unsat spec" ){
    val phi = bd.bool( false )
    val encoder = new AssignmentStrategyEncoder()
    val fullSpec = encoder( Set("x"), phi, complete = true )

    val spec = encoder( Set("x"), phi, complete = false)
    assert( fullSpec.nonEmpty )

    assert( (new SMTInterface())(spec, encoder.m_varSym).isEmpty )

  }

  test( "Test Next = single asgn, no connectives" ){
    val next = bd.primeInSingleton( n_x, n_S )

    val decls = Seq( TlaOperDecl( "Next", List(), next ), TlaVarDecl( "x" ) )

    val symbNexts = testFromDecls( decls )
  }

  test( "Test non-compliant SMT spec" ){
    val spec = "( declare-fun f ( Int ) Int )\n ( declare-fun g ( Int ) Int )\n" +
      "(assert ( = ( f 0 ) ( g 0 ) ) )"
    val smt = new SMTInterface()

    val strat = smt(spec, "X")

    assert( strat.isEmpty )

  }

  test( "Test no strat" ){
//    val next = bd.primeInSingleton( n_x, n_S )

    val next = bd.eql( bd.prime( n_x ), n_y )

    val decls = Seq( TlaOperDecl( "Next", List(), next ), TlaVarDecl( "x" ), TlaVarDecl( "z" ) )

    assertThrows[AssignmentException]( testFromDecls( decls ) )

  }

  test( "Test no Next" ){
    val next = bd.primeInSingleton( n_x, n_S )

    val decls = Seq( TlaOperDecl( "Next", List(), next ), TlaVarDecl( "x" ) )

    assertThrows[AssignmentException]( testFromDecls( decls, "NotNext" ) )

  }

  test( "Test Selections" ){
    val symbNexts = testFromFile( "Selections.tla" )
  }

  test( "Test Paxos (simplified)" ){
    val symbNexts = testFromFile( "Paxos.tla" )
  }

  test("Test ITE_CASE") {
    val symbNexts = testFromFile( "ITE_CASE.tla" )
  }

  test("Test EWD840") {
    val symbNexts = testFromFile( "EWD840.tla" )
  }

  test( "AST" ){
    val symbNexts = testFromFile( "ast.tla" )
  }

  test( "test1" ) {
    val symbNexts = testFromFile( "test1.tla" )
  }

  test( "SimpTendermit1" ) {
    val symbNexts = testFromFile( "SimpTendermit1.tla" )
    val symbNexts2 = testFromFile( "SimpTendermit1.tla", "NextNoFaults" )
  }
}
