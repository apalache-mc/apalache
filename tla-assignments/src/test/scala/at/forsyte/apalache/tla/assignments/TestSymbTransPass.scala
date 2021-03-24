package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.storage.{BodyMapFactory, ChangeListener}
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.transformations.standard._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.pp.{Desugarer, UniqueNameGenerator}
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
    val gen = new UniqueNameGenerator
    val preprocessed = ModuleByExTransformer(Desugarer(gen, tracker))(explLetIn)

    val vars = preprocessed.varDeclarations.map(_.name)

    SymbolicTransitionExtractor(tracker)(vars, preprocessed.operDeclarations.find(_.name == p_next).get.body)
  }

  test("Test labelsAt") {
    val gen = new SymbTransGenerator(TrackerWithListeners())

    assert(gen.helperFunctions.labelsAt(NullEx, Map.empty[UID, Set[Set[UID]]]).isEmpty)
  }

  test("Test Complete Spec return + unsat spec") {
    val phi = tla.bool(false)
    val encoder = new AssignmentStrategyEncoder()
    val fullSpec = encoder(Set("x"), phi, complete = true)

    val spec = encoder(Set("x"), phi, complete = false)
    assert(fullSpec.nonEmpty)

    assert((new SMTInterface())(spec, encoder.m_varSym).isEmpty)

  }

  test("Test Next = single asgn, no connectives") {
    val next = tla.primeInSingleton(n_x, n_S)

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
    val next = tla.eql(tla.prime(n_x), n_y)
    val decls = Seq(TlaOperDecl("Next", List(), next), TlaVarDecl("x"), TlaVarDecl("z"))
    val trans = testFromDecls(decls)
    assert(trans.isEmpty)
  }
}
