package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.search.BfsStrategy
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.BmcOper
import at.forsyte.apalache.tla.lir.storage.ChangeListener
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfter, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestModelChecker extends FunSuite with BeforeAndAfter {
  private var typeFinder: TrivialTypeFinder = new TrivialTypeFinder()
  private var exprGradeStore: ExprGradeStore = new ExprGradeStoreImpl()
  private var hintsStore: FormulaHintsStoreImpl = new FormulaHintsStoreImpl()
  private var changeListener: ChangeListener = new ChangeListener()
  private var sourceStore: SourceStore = _

  before {
    // initialize the model checker
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
    val dummyModule = new TlaModule("root", List())
    val checkerInput =
      new CheckerInput(dummyModule, initTrans, nextTrans, None, List.empty)
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init, deadlock") {
    // x' \in {2} /\ x' \in {1}
    val initTrans = List(tla.and(mkAssign("x", 2), mkNotAssign("x", 1)))
    val nextTrans = List(mkAssign("x", 2))
    val dummyModule = new TlaModule("root", List())
    val checkerInput =
      new CheckerInput(dummyModule, initTrans, nextTrans, None, List.empty)
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init, 2 options, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    val nextTrans = List(mkAssign("x", 2))
    val dummyModule = new TlaModule("root", List())
    val checkerInput =
      new CheckerInput(dummyModule, initTrans, nextTrans, None, List.empty)
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 0)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 1 step, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    val dummyModule = new TlaModule("root", List())
    val checkerInput =
      new CheckerInput(dummyModule, initTrans, nextTrans, None, List.empty)
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 1)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 1 step, formula hint") {
    // x' \in {1}
    val initTrans = List(mkAssign("x", 1))
    // x < 10 /\ x' \in {x + 1}
    val nextTrans =
      List(
          tla.and(
              tla.lt(tla.name("x"), tla.int(10)),
              mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
          )
      )
    ///
    val dummyModule = new TlaModule("root", List())
    val checkerInput =
      new CheckerInput(dummyModule, initTrans, nextTrans, None, List.empty)

    // Add the hint. We cannot check in the test, whether the hints was actually used.
    // We only check that the checker works in presence of hints.
    hintsStore.store.put(nextTrans.head.ID, FormulaHintsStore.HighAnd())
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 1)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("determinstic Init + 2 steps (regression)") {
    // y' \in {1} /\ x' \in {1}
    val initTrans = List(tla.and(mkAssign("y", 1), mkAssign("x", 1)))
    // y' \in {y + 1} /\ x' \in {x + 1}
    val nextTrans = List(
        tla.and(
            mkAssign("y", tla.plus(tla.name("y"), tla.int(1))),
            mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
        )
    )
    ///
    val dummyModule = new TlaModule("root", List())
    val inv = tla.eql(
        tla.eql(tla.int(3), tla.name("x")),
        tla.eql(tla.int(3), tla.name("y"))
    ) ////

    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        None,
        List((inv, tla.not(inv)))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 2)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + 2 steps with LET-IN") {
    // x' \in {1}
    val initTrans = List(mkAssign("x", 1))
    // LET A == 1 + x IN x' \in { A + 1 }
    val aDecl = TlaOperDecl("A", List(), tla.plus(tla.int(1), tla.name("x")))

    val letIn = tla.letIn(tla.plus(tla.appDecl(aDecl), tla.int(1)), aDecl)

    val nextTrans = List(mkAssign("x", letIn))
    ///
    val dummyModule = new TlaModule("root", List())
    val inv = tla.not(tla.eql(tla.int(4), tla.name("x")))

    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        None,
        List((inv, tla.not(inv)))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 2)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 1 step, deadlock") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x > 3 /\ x' \in {x + 1}
    val nextTrans = List(
        tla.and(
            tla.gt(tla.name("x"), tla.int(3)),
            mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
        )
    )
    val dummyModule = new TlaModule("root", List())
    val checkerInput =
      new CheckerInput(dummyModule, initTrans, nextTrans, None, List())
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 1)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init + Next, 10 steps, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    val dummyModule = new TlaModule("root", List())
    val checkerInput =
      new CheckerInput(dummyModule, initTrans, nextTrans, None, List())
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 10)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 10 steps, deadlock") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x < 10 /\ x' \in {x + 1}
    val nextTrans = List(
        tla.and(
            tla.lt(tla.name("x"), tla.int(10)),
            mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
        )
    )
    val dummyModule = new TlaModule("root", List())
    val checkerInput =
      new CheckerInput(dummyModule, initTrans, nextTrans, None, List())
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 10)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init + Next + Inv, 10 steps, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 100
    val inv = tla.lt(tla.name("x"), tla.int(100))
    val dummyModule = new TlaModule("root", List())
    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        None,
        List((inv, tla.not(inv)))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 10)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next + Inv, 10 steps, learnFromUnsat, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 100
    val inv = tla.lt(tla.name("x"), tla.int(100))
    val dummyModule = new TlaModule("root", List())
    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        None,
        List((inv, tla.not(inv)))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 10)
    val tuning = Map("search.invariant.learnFromUnsat" -> "true")
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        tuning,
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next + Inv, 10 steps, !search.invariant.split, OK") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 100
    val inv = tla.lt(tla.name("x"), tla.int(100))
    val dummyModule = new TlaModule("root", List())
    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        None,
        List((inv, tla.not(inv)))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 10)
    val tuning = Map("search.invariant.split" -> "false")
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        tuning,
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next + Inv, 10 steps, error") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 5
    val inv = tla.lt(tla.name("x"), tla.int(5))
    val dummyModule = new TlaModule("root", List())
    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        None,
        List((inv, tla.not(inv)))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 10)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init + Next + Inv, 3 steps, error, edge case") {
    // the invariant is violated in the last state of a bounded execution

    // x' \in {0}
    val initTrans = List(mkAssign("x", 0))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x /= 3
    val inv = tla.not(tla.eql(tla.name("x"), tla.int(3)))
    val dummyModule = new TlaModule("root", List())
    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        None,
        List((inv, tla.not(inv)))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 3)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init + Next + Inv, 2 steps, no error, edge case") {
    // the invariant is violated in the last state of a bounded execution

    // x' \in {0}
    val initTrans = List(mkAssign("x", 0))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x /= 3
    val inv = tla.not(tla.eql(tla.name("x"), tla.int(3)))
    val dummyModule = new TlaModule("root", List())
    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        None,
        List((inv, tla.not(inv)))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 2)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next + Inv, 10 steps, and invariantFilter") {
    // x' \in {2} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' \in {x + 1}
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 5
    val inv = tla.lt(tla.name("x"), tla.int(5))
    val dummyModule = new TlaModule("root", List())
    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        None,
        List((inv, tla.not(inv)))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 10)
    // We require the invariant to be checked only after the second step. So we will miss invariant violation.
    val tuning = Map("search.invariantFilter" -> "2")
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        tuning,
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 3 steps, non-determinism but no deadlock") {
    // x' \in {1}
    val initTrans = List(mkAssign("x", 1))
    // x' \in {x + 1} \/ x > 100 /\ x' \in {x}
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 =
      tla.and(tla.gt(tla.name("x"), tla.int(100)), mkAssign("x", tla.name("x")))
    val nextTrans = List(trans1, trans2)
    val dummyModule = new TlaModule("root", List())
    val checkerInput =
      new CheckerInput(dummyModule, initTrans, nextTrans, None, List())
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 3)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
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
    val init = tla.and(
        mkAssign("x", tla.enumSet(tla.int(2))),
        mkAssign("y", tla.enumSet(tla.int(10)))
    )

    // as KerA+ does not have setminus, we use a filter here
    def setminus(setName: String, boundName: String, intVal: Int): TlaEx = {
      tla.filter(
          tla.name(boundName),
          tla.name(setName),
          tla.not(tla.eql(tla.name(boundName), tla.int(intVal)))
      )
    }

    // Next == \/ x' = x \cup {2} /\ y' = y \setminus {11}
    //         \/ x' = x \setminus {2} /\ y' = y \cup {11}
    val next1 =
      tla.and(
          mkAssign("x", tla.cup(tla.name("x"), tla.enumSet(tla.int(2)))),
          mkAssign("y", setminus("y", "t1", 11))
      )
    ///
    ///
    val next2 =
      tla.and(
          mkAssign("x", setminus("x", "t2", 2)),
          mkAssign("y", tla.cup(tla.name("y"), tla.enumSet(tla.int(11))))
      ) ///

    // Inv ==  11 \in y <=> 2 \notin x
    val inv = tla.eql(
        tla.in(tla.int(11), tla.name("y")),
        tla.not(tla.in(tla.int(2), tla.name("x")))
    ) ////

    val dummyModule = new TlaModule("root", List())
    val checkerInput = new CheckerInput(
        dummyModule,
        List(init),
        List(next1, next2),
        None,
        List((inv, tla.not(inv)))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 2)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 10 steps, non-determinism in init and next") {
    // x' \in {0} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 0), mkAssign("x", 1))
    // x' \in {x + 1} \/ x > 10 /\ x' \in {x}
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 =
      tla.and(tla.gt(tla.name("x"), tla.int(10)), mkAssign("x", tla.name("x")))
    val nextTrans = List(trans1, trans2)
    val notInv = tla.gt(tla.prime(tla.name("x")), tla.int(10)) // ~(x <= 10)
    val dummyModule = new TlaModule("root", List())
    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        None,
        List((tla.not(notInv), notInv))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 10)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("cInit + Init + Next, 10 steps") {
    // x' \in {0} \/ x' \in {1}
    val initTrans = List(mkAssign("x", 0), mkAssign("x", 1))
    // x' \in {x + 1} \/ x > 10 /\ x' \in {x}
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 =
      tla.and(tla.gt(tla.name("x"), tla.int(10)), mkAssign("x", tla.name("x")))
    val nextTrans = List(trans1, trans2)
    // a constant initializer: \E t \in { 20, 10 }: N' \in {t}
    val cInit =
      OperEx(
          BmcOper.skolem,
          tla.exists(
              tla.name("t"),
              tla.enumSet(tla.int(20), tla.int(10)),
              tla.in(tla.prime(tla.name("N")), tla.enumSet(tla.name("t")))
          )
      ) ////

    val notInv = tla.gt(tla.prime(tla.name("x")), tla.name("N")) // ~(x <= N)
    val dummyModule =
      new TlaModule("root", List(TlaConstDecl("N"), TlaVarDecl("x")))
    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        Some(cInit),
        List((tla.not(notInv), notInv))
    )
    // initialize the model checker
    val strategy = new BfsStrategy(checkerInput, stepsBound = 10)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        Map(),
        debug = false,
        profile = false
    )
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
    val notInv = tla.gt(tla.name("x"), tla.int(11)) // ~(x <= 11)
    val dummyModule = new TlaModule("root", List())
    val checkerInput = new CheckerInput(
        dummyModule,
        initTrans,
        nextTrans,
        None,
        List((tla.not(notInv), notInv))
    )
    // initialize the model checker
    val filter = "0,0,0,0,0,0,0,0,0,0,0" // execute initTrans once and onlytrans1 10 times
    val tuning = Map("search.transitionFilter" -> filter)
    val strategy = new BfsStrategy(checkerInput, stepsBound = 10)
    val checker = new ModelChecker(
        typeFinder,
        hintsStore,
        changeListener,
        exprGradeStore,
        sourceStore,
        checkerInput,
        strategy,
        tuning,
        debug = false,
        profile = false
    )
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  private def mkAssign(name: String, value: Int) =
    tla.assignPrime(tla.name(name), tla.int(value))

  private def mkAssign(name: String, rhs: TlaEx) =
    tla.assignPrime(tla.name(name), rhs)

  private def mkNotAssign(name: String, value: Int) =
    tla.primeEq(tla.name(name), tla.int(value))

  private def mkNotAssign(name: String, rhs: TlaEx) =
    tla.primeEq(tla.name(name), rhs)
}
