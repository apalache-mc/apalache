package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.imp.declarationsFromFile
import at.forsyte.apalache.tla.lir.storage.{BodyMapFactory, ChangeListener}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir.{Builder => bd, _}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.pp.Desugarer
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbTransPass extends FunSuite with TestingPredefs {
  val testFolderPath = "src/test/resources/assignmentSolver/"

  def testFromNext(p_next: TlaEx): Seq[SymbTrans] = {
    testFromDecls(Seq(TlaOperDecl("Next", List(), p_next)))
  }

  def testFromDecls(p_decls: Seq[TlaDecl], p_next: String = "Next"): Seq[SymbTrans] = {
    val fakeModule = new TlaModule("test", p_decls)
    val srcDB = new ChangeListener

    val tracker = TrackerWithListeners(srcDB)
    val renaming = new IncrementalRenaming(tracker)
    val uniqueVarDecls =
      new TlaModule(
          fakeModule.name,
          renaming.syncAndNormalizeDs(fakeModule.declarations).toSeq
      )

    val bodyMap = BodyMapFactory.makeFromDecls(uniqueVarDecls.operDeclarations)
    val inlined = ModuleByExTransformer(InlinerOfUserOper(bodyMap, tracker))(uniqueVarDecls)
    val explLetIn = ModuleByExTransformer(LetInExpander(tracker, keepNullary = false))(inlined)
    val afterDesugarer = ModuleByExTransformer(Desugarer(tracker))(explLetIn)
    val preprocessed = ModuleByExTransformer(PrimedEqualityToMembership(tracker))(afterDesugarer)

    val vars = preprocessed.varDeclarations.map(_.name)

    SymbolicTransitionExtractor(tracker)(vars, preprocessed.operDeclarations.find(_.name == p_next).get.body)
  }

  def testFromFile(p_file: String, p_next: String = "Next"): Seq[SymbTrans] = {

    val decls = declarationsFromFile(testFolderPath + p_file)

    val ret = testFromDecls(decls, p_next)

    //    val saveWriter = new PrintWriter( new File( testFolderPath + "SymbNexts" + p_file ) )

    //    ret.foreach( x => saveWriter.println( "%s : \n %s\n".format( x._1.map( UniqueDB.get ) , x._2 ) ) )

    //    saveWriter.close()

    ret
  }

  test("Test labelsAt") {
    val gen = new SymbTransGenerator(TrackerWithListeners())

    assert(gen.helperFunctions.labelsAt(NullEx, Map.empty[UID, Set[Set[UID]]]).isEmpty)
  }

  test("Test Complete Spec return + unsat spec") {
    val phi = bd.bool(false)
    val encoder = new AssignmentStrategyEncoder()
    val fullSpec = encoder(Set("x"), phi, complete = true)

    val spec = encoder(Set("x"), phi, complete = false)
    assert(fullSpec.nonEmpty)

    assert((new SMTInterface())(spec, encoder.m_varSym).isEmpty)

  }

  test("Test Next = single asgn, no connectives") {
    val next = bd.primeInSingleton(n_x, n_S)

    val decls = Seq(TlaOperDecl("Next", List(), next), TlaVarDecl("x"))

    val symbNexts = testFromDecls(decls)
  }

  test("Test non-compliant SMT spec") {
    val spec = "( declare-fun f ( Int ) Int )\n ( declare-fun g ( Int ) Int )\n" +
      "(assert ( = ( f 0 ) ( g 0 ) ) )"
    val smt = new SMTInterface()

    val strat = smt(spec, "X")

    assert(strat.isEmpty)

  }

  test("Test no strat") {
    val next = bd.eql(bd.prime(n_x), n_y)
    val decls = Seq(TlaOperDecl("Next", List(), next), TlaVarDecl("x"), TlaVarDecl("z"))
    val trans = testFromDecls(decls)
    assert(trans.isEmpty)
  }

  ignore("Test no Next") {
    // the new version of SymbolicTransitionExtractor accepts an expression, so nothing to test here
    // TODO: remove this test
    val next = bd.primeInSingleton(n_x, n_S)
    val decls = Seq(TlaOperDecl("Next", List(), next), TlaVarDecl("x"))
    assertThrows[AssignmentException](testFromDecls(decls, "NotNext"))
  }

  test("Test Selections") {
    val symbNexts = testFromFile("Selections.tla")
  }

  test("Test Paxos (simplified)") {
    val symbNexts = testFromFile("Paxos.tla")
  }

  test("Test ITE_CASE") {
    val symbNexts = testFromFile("ITE_CASE.tla")
  }

  test("Test EWD840") {
    val symbNexts = testFromFile("EWD840.tla")
  }

  test("AST") {
    val symbNexts = testFromFile("ast.tla")
  }

  test("test1") {
    val symbNexts = testFromFile("test1.tla")
  }

  test("SimpT1") {
    val symbNexts = testFromFile("SimpT1.tla")
    val symbNexts2 = testFromFile("SimpT1.tla", "NextNoFaults")
  }
}
