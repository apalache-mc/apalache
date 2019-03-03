package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.search.BfsStrategy
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{EnvironmentHandlerGenerator, TlaEx, TlaModule, TlaOperDecl}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfter, FunSuite}

import scala.io.Source

@RunWith(classOf[JUnitRunner])
class TestBfsChecker extends FunSuite with BeforeAndAfter {
  private var frexStore: FreeExistentialsStoreImpl = new FreeExistentialsStoreImpl()
  private var typeFinder: TrivialTypeFinder = new TrivialTypeFinder()
  private var exprGradeStore: ExprGradeStore = new ExprGradeStoreImpl()
  private var hintsStore: FormulaHintsStoreImpl = new FormulaHintsStoreImpl()
  private var sourceStore: SourceStore = new SourceStore()

  before {
    // initialize the model checker
    frexStore = new FreeExistentialsStoreImpl()
    typeFinder = new TrivialTypeFinder()
    exprGradeStore = new ExprGradeStoreImpl()
    sourceStore = new SourceStore()
  }

  after {
    typeFinder.reset(Map())
  }

  test("Init, OK") {
    // x' \in {2}
    val initTrans = List(mkAssign("x", 2))
    val nextTrans = List(mkAssign("x", 2))
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, None)
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore, checkerInput,
      stepsBound = 0, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init, deadlock") {
    // x' \in {2} /\ x' \in {1}
    val initTrans = List(tla.and(mkAssign("x", 2), mkAssign("x", 1)))
    val nextTrans = List(mkAssign("x", 2))
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, None)
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore, checkerInput,
      stepsBound = 0, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init, 2 options, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    val nextTrans = List(mkAssign("x", 2))
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, None)
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore, checkerInput,
      stepsBound = 0, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 1 step, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, None)
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore, checkerInput,
      stepsBound = 1, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 1 step, formula hint") {
    // x' \in {1}
    val initTrans = List(mkAssign("x", 1))
    // x < 10 /\ x' \in {x + 1}
    val nextTrans =
      List(tla.and(
        tla.lt(tla.name("x"), tla.int(10)),
        mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
      )///
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, None)

    // Add the hint. We cannot check in the test, whether the hints was actually used.
    // We only check that the checker works in presence of hints.
    hintsStore.store.put(nextTrans.head.ID, FormulaHintsStore.HighAnd())
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore, checkerInput,
      stepsBound = 1, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("determinstic Init + 2 steps (regression)") {
    // y' \in {1} /\ x' \in {1}
    val initTrans = List(tla.and(mkAssign("y", 1), mkAssign("x", 1)))
    // y' \in {y + 1} /\ x' \in {x + 1}
    val nextTrans = List(tla.and(
      mkAssign("y", tla.plus(tla.name("y"), tla.int(1))),
      mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    ))///
    val dummyModule = new TlaModule("root", List(), List())
    val notInv = tla.not(tla.equiv(
      tla.eql(tla.int(3), tla.prime(tla.name("x"))),
      tla.eql(tla.int(3), tla.prime(tla.name("y")))
    ))////

    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, Some(notInv))
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore, checkerInput,
      stepsBound = 2, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 1 step, deadlock") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x > 3 /\ x' \in {x + 1}
    val nextTrans = List(
      tla.and(tla.gt(tla.name("x"), tla.int(3)),
        mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))))
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, None)
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore, checkerInput,
      stepsBound = 1, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init + Next, 10 steps, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, None)
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore, checkerInput,
      stepsBound = 10, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 10 steps, deadlock") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x < 10 /\ x' \in {x + 1}
    val nextTrans = List(
      tla.and(tla.lt(tla.name("x"), tla.int(10)),
        mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))))
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, None)
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore, checkerInput,
      stepsBound = 10, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init + Next + Inv, 10 steps, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 100
    val notInv = tla.not(tla.lt(tla.prime(tla.name("x")), tla.int(100)))
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, Some(notInv))
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore, checkerInput,
      stepsBound = 10, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next + Inv, 10 steps, error") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(tla.or(mkAssign("x", 2), mkAssign("x", 1)))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 5
    val notInv = tla.not(tla.lt(tla.prime(tla.name("x")), tla.int(5)))
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, Some(notInv))
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore, checkerInput,
      stepsBound = 10, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init + Next, 3 steps, non-determinism but no deadlock") {
    // x' \in {1}
    val initTrans = List(mkAssign("x", 1))
    // x' \in {x + 1} \/ x > 100 /\ x' \in {x}
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 = tla.and(tla.gt(tla.name("x"), tla.int(100)),
      mkAssign("x", tla.name("x")))
    val nextTrans = List(trans1, trans2)
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, None)
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore,
      checkerInput, stepsBound = 3, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next + Inv, 2 steps, set assignments") {
    // sets require an explicit equality, and that is where picking the next state may fail
    // Init == x \in {2} /\ y \in {10}
    // Next == \/ x' = x \cup {2} /\ y' = y \setminus {11}
    //         \/ x' = x \setminus {2} /\ y' = y \cup {11}
    // Inv ==  11 \in y <=> 2 \notin x

    // Init == x' = {2} /\ y = {10}
    val init = tla.and(mkAssign("x", tla.enumSet(tla.int(2))),
      mkAssign("y", tla.enumSet(tla.int(10))))

    // Next == \/ x' = x \cup {2} /\ y' = y \setminus {11}
    //         \/ x' = x \setminus {2} /\ y' = y \cup {11}
    val next1 =
    tla.and(
      mkAssign("x", tla.cup(tla.name("x"), tla.enumSet(tla.int(2)))),
      mkAssign("y", tla.setminus(tla.name("y"), tla.enumSet(tla.int(11))))
    )///
    ///
    val next2 =
      tla.and(
        mkAssign("x", tla.setminus(tla.name("x"), tla.enumSet(tla.int(2)))),
        mkAssign("y", tla.cup(tla.name("y"), tla.enumSet(tla.int(11))))
      ) ///

    // Inv ==  11 \in y <=> 2 \notin x
    val notInv = tla.not(tla.equiv(
      tla.in(tla.int(11), tla.prime(tla.name("y"))),
      tla.notin(tla.int(2), tla.prime(tla.name("x")))
    ))////

    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, List(init), List(next1, next2), Some(notInv))
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore,
      sourceStore, checkerInput, stepsBound = 2, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 10 steps, non-determinism in init and next") {
    // x' \in {0} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 0), mkAssign("x", 1))
    // x' \in {x + 1} \/ x > 10 /\ x' \in {x}
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 = tla.and(tla.gt(tla.name("x"), tla.int(10)),
      mkAssign("x", tla.name("x")))
    val nextTrans = List(trans1, trans2)
    val notInv = tla.gt(tla.prime(tla.name("x")), tla.int(10)) // ~(x <= 10)
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, Some(notInv))
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore,
      checkerInput, stepsBound = 10, "", strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init + Next, 10 steps and filter") {
    // x' \in {0}
    val initTrans = List(mkAssign("x", 0))
    // x' \in {x + 1} \/ x' \in {x + 2}
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 = mkAssign("x", tla.plus(tla.name("x"), tla.int(2)))
    val nextTrans = List(trans1, trans2)
    val notInv = tla.gt(tla.prime(tla.name("x")), tla.int(11)) // ~(x <= 11)
    val dummyModule = new TlaModule("root", List(), List())
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, Some(notInv))
    // initialize the model checker
    val filter = "0,0,0,0,0,0,0,0,0,0,0" // execute initTrans once and onlytrans1 10 times
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new BfsChecker(typeFinder, frexStore, hintsStore, exprGradeStore, sourceStore,
      checkerInput, stepsBound = 10, filter = filter, strategy, debug = false, profile = false)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  ////////////////////////////////////////////////////////////////////
  private def importTla(name: String, text: String) = {
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, new SourceStore)
      .loadFromSource(name, Source.fromString(text))
    val mod = expectSingleModule(name, rootName, modules)
    val init = mod.declarations.find(_.name == "Init").get
    val next = mod.declarations.find(_.name == "Next").get
    (mod, init, next)
  }

  private def expectOperatorDeclaration(expectedName: String, idx: Int, mod: TlaModule): TlaOperDecl = {
    mod.declarations(idx) match {
      case decl: TlaOperDecl =>
        assert(expectedName == decl.name)
        decl

      case _ =>
        fail("Expected operator " + expectedName + " at position " + idx)
    }
  }

  // copied from TestSanyImporter
  private def expectSingleModule(expectedRootName: String, rootName: String,
                                 modules: Map[String, TlaModule]): TlaModule = {
    assert(expectedRootName == rootName)
    assert(1 <= modules.size)
    val root = modules.get(rootName)
    root match {
      case Some(mod) =>
        mod

      case None =>
        fail("Module " + rootName + " not found")
    }
  }

  private def mkAssign(name: String, value: Int) =
    tla.in(tla.prime(tla.name(name)), tla.enumSet(tla.int(value)))

  private def mkAssign(name: String, rhs: TlaEx) =
    tla.in(tla.prime(tla.name(name)), tla.enumSet(rhs))
}
