package at.forsyte.apalache.tla.bmcmt

import java.io.File
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams.InvariantMode
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import at.forsyte.apalache.tla.bmcmt.trex.{
  FilteredTransitionExecutor, IncrementalExecutionContext, TransitionExecutorImpl
}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.BmcOper
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfter, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestSeqModelChecker extends FunSuite with BeforeAndAfter {
  private var solver: RecordingSolverContext =
    RecordingSolverContext.createZ3(None, SolverConfig(debug = false, profile = false, 0))
  private var rewriter = new SymbStateRewriterImpl(solver, new ExprGradeStoreImpl)

  before {
    // initialize the model checker
    solver = RecordingSolverContext.createZ3(None, SolverConfig(debug = false, profile = false, 0))
    rewriter = new SymbStateRewriterImpl(solver, new ExprGradeStoreImpl)
  }

  private def mkModuleWithX(): TlaModule = {
    new TlaModule("root", List(TlaVarDecl("x")))
  }

  private def mkModuleWithXandY(): TlaModule = {
    new TlaModule("root", List(TlaVarDecl("x"), TlaVarDecl("y")))
  }

  test("Init + Inv => OK") {
    // x' <- 2
    val initTrans = List(mkAssign("x", 2))
    val nextTrans = List(mkAssign("x", 2))
    val notInv = tla.gt(tla.name("x"), tla.int(10))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((tla.not(notInv), notInv)))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, new File("."), Map(), false)
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Inv => ERR") {
    // x' <- 2
    val initTrans = List(mkAssign("x", 2))
    val nextTrans = List(mkAssign("x", 2))
    val notInv = tla.lt(tla.name("x"), tla.int(10))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((tla.not(notInv), notInv)))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, new File("."), Map(), false)
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("ConstInit + Init => OK") {
    // N' <- 10
    val cinit = mkAssign("N", 10)
    // x' <- N
    val initTrans = List(mkAssign("x", tla.name("N")))
    val nextTrans = List(mkAssign("x", tla.name("N")))
    val module = new TlaModule("root", List(TlaConstDecl("N"), TlaVarDecl("x")))
    val notInv = tla.lt(tla.name("x"), tla.int(10))

    val checkerInput = new CheckerInput(module, initTrans, nextTrans, Some(cinit), List((tla.not(notInv), notInv)))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, new File("."), Map(), false)
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("ConstInit + Init => ERR") {
    // N' <- 10
    val cinit = mkAssign("N", 5)
    // x' <- N
    val initTrans = List(mkAssign("x", tla.name("N")))
    val nextTrans = List(mkAssign("x", tla.name("N")))
    val module = new TlaModule("root", List(TlaConstDecl("N"), TlaVarDecl("x")))
    val notInv = tla.lt(tla.name("x"), tla.int(10))

    val checkerInput = new CheckerInput(module, initTrans, nextTrans, Some(cinit), List((tla.not(notInv), notInv)))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, new File("."), Map(), false)
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init, deadlock") {
    // x' <- 2 /\ x' <- 1
    val initTrans = List(tla.and(mkAssign("x", 2), mkNotAssign("x", 1)).untyped())
    val nextTrans = List(mkAssign("x", 2))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List.empty)
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init, 2 options, OK") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    val nextTrans = List(mkAssign("x", 2))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List.empty)
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next x 1 => OK") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List.empty)
    val params = new ModelCheckerParams(checkerInput, stepsBound = 1, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next x 10 + Inv (before + no-all-enabled) => ERR") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 5
    val inv = tla.lt(tla.name("x"), tla.int(5))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((inv, tla.not(inv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    params.discardDisabled = true
    params.invariantMode = InvariantMode.BeforeJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init + Next x 10 + Inv (before + all-enabled) => ERR") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 5
    val inv = tla.lt(tla.name("x"), tla.int(5))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((inv, tla.not(inv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    params.discardDisabled = false
    params.invariantMode = InvariantMode.BeforeJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init + Next x 10 + Inv (after + all-enabled) => ERR") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 5
    val inv = tla.lt(tla.name("x"), tla.int(5))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((inv, tla.not(inv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    params.discardDisabled = false
    params.invariantMode = InvariantMode.AfterJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init + Next x 10 + Inv (after + no-all-enabled) => ERR") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 5
    val inv = tla.lt(tla.name("x"), tla.int(5))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((inv, tla.not(inv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    params.discardDisabled = true
    params.invariantMode = InvariantMode.AfterJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init + Next x 2 (LET-IN) + Inv => ERR") {
    // x' <- 1
    val initTrans = List(mkAssign("x", 1))
    // x' <- x + 1
    val assign = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val nextTrans = List(assign)
    // x < 3
    val lt = tla.lt(tla.name("x"), tla.int(3))
    val letIn = tla.letIn(tla.appOp(tla.name("Foo")), tla.declOp("Foo", lt).untypedOperDecl())
    val inv = letIn
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((inv, tla.not(inv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 2, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("determinstic Init + 2 steps (regression)") {
    // y' <- 1 /\ x' <- 1
    val initTrans = List(tla.and(mkAssign("y", 1), mkAssign("x", 1)).untyped())
    // y' <- y + 1 /\ x' <- x + 1
    val nextTrans = List(
        tla
          .and(
              mkAssign("y", tla.plus(tla.name("y"), tla.int(1))),
              mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
          )
          .untyped()) ///
    val inv = tla.eql(
        tla.eql(tla.int(3), tla.name("x")),
        tla.eql(tla.int(3), tla.name("y"))
    ) ////

    val checkerInput = new CheckerInput(mkModuleWithXandY(), initTrans, nextTrans, None, List((inv, tla.not(inv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 2, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next x 1 => deadlock") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x > 3 /\ x' <- x + 1
    val nextTrans =
      List(tla.and(tla.gt(tla.name("x"), tla.int(3)), mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))).untyped())
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List())
    val params = new ModelCheckerParams(checkerInput, stepsBound = 1, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init + Next, 10 steps, OK") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List())
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next x 10 => deadlock") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x < 10 /\ x' <- x + 1
    val nextTrans =
      List(tla.and(tla.lt(tla.name("x"), tla.int(10)), mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))).untyped())
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List())
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Deadlock == outcome)
  }

  test("Init + Next + Inv x 10 => OK") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 100
    val inv = tla.lt(tla.name("x"), tla.int(100))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((inv, tla.not(inv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next + Inv x 3 => ERR, edge case") {
    // the invariant is violated in the last state of a bounded execution

    // x' <- 0
    val initTrans = List(mkAssign("x", 0))
    // x' <- x + 1
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x /= 3
    val inv = tla.not(tla.eql(tla.name("x"), tla.int(3)))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((inv, tla.not(inv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 3, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init + Next + Inv x 2 => OK, edge case") {
    // the invariant is violated in the last state of a bounded execution
    // x' <- 0
    val initTrans = List(mkAssign("x", 0))
    // x' <- x + 1
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x /= 3
    val inv = tla.not(tla.eql(tla.name("x"), tla.int(3)))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((inv, tla.not(inv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 2, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next + Inv x 10 and invariantFilter => OK") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = List(mkAssign("x", tla.plus(tla.name("x"), tla.int(1))))
    // x < 5
    val inv = tla.lt(tla.name("x"), tla.int(5))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((inv, tla.not(inv))))
    // initialize the model checker
    // We require the invariant to be checked only after the second step. So we will miss invariant violation.
    val tuning = Map("search.invariantFilter" -> "2")
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), tuning, false)
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex =
      new FilteredTransitionExecutor("", params.invFilter, new TransitionExecutorImpl(params.consts, params.vars, ctx))
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next x 3 + non-determinism => no deadlock") {
    // x' <- 1
    val initTrans = List(mkAssign("x", 1))
    // x' <- x + 1 \/ x > 100 /\ x' <- x
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 = tla.and(tla.gt(tla.name("x"), tla.int(100)), mkAssign("x", tla.name("x"))).untyped()
    val nextTrans = List(trans1, trans2)
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List())
    val params = new ModelCheckerParams(checkerInput, stepsBound = 3, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next, 10 steps, non-determinism in init and next") {
    // x' <- 0 \/ x' <- 1
    val initTrans = List(mkAssign("x", 0), mkAssign("x", 1))
    // x' <- x + 1 \/ x > 10 /\ x' <- x
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 = tla.and(tla.gt(tla.name("x"), tla.int(10)), mkAssign("x", tla.name("x"))).untyped()
    val nextTrans = List(trans1, trans2)
    val notInv = tla.gt(tla.name("x"), tla.int(10)) // ~(x <= 10)
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((tla.not(notInv), notInv)))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("cInit + Init + Next, 10 steps") {
    // x' <- 0 \/ x' <- 1
    val initTrans = List(mkAssign("x", 0), mkAssign("x", 1))
    // x' <- x + 1 \/ x > 10 /\ x' <- x
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 = tla.and(tla.gt(tla.name("x"), tla.int(10)), mkAssign("x", tla.name("x"))).untyped()
    val nextTrans = List(trans1, trans2)
    // a constant initializer: \E t \in { 20, 10 }: N' \in {t}
    val cInit =
      OperEx(BmcOper.skolem,
          tla.exists(
              tla.name("t"),
              tla.enumSet(tla.int(20), tla.int(10)),
              mkAssign("N", tla.name("t"))
          )) ////

    val notInv = tla.gt(tla.name("x"), tla.name("N")) // ~(x <= N)
    val dummyModule = new TlaModule("root", List(TlaConstDecl("N"), TlaVarDecl("x")))
    val checkerInput = new CheckerInput(dummyModule, initTrans, nextTrans, Some(cInit), List((tla.not(notInv), notInv)))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init + Next, 10 steps and filter") {
    // x' <- 0
    val initTrans = List(mkAssign("x", 0))
    // x' <- x + 1 \/ x' <- x + 2
    val trans1 = mkAssign("x", tla.plus(tla.name("x"), tla.int(1)))
    val trans2 = mkAssign("x", tla.plus(tla.name("x"), tla.int(2)))
    val nextTrans = List(trans1, trans2)
    val notInv = tla.gt(tla.name("x"), tla.int(11)) // ~(x <= 11)
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, List((tla.not(notInv), notInv)))
    // initialize the model checker
    val filter = "0,0,0,0,0,0,0,0,0,0,0" // old syntax
    val tuning = Map.empty[String, String] // Map("search.transitionFilter" -> filter)
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), tuning, false)
    val ctx = new IncrementalExecutionContext(rewriter)
    val impl = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val trex = new FilteredTransitionExecutor("([0-9]|10)->0", "", impl)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  private def mkAssign(name: String, value: Int): TlaEx =
    tla.assignPrime(tla.name(name), tla.int(value))

  private def mkAssign(name: String, rhs: TlaEx): TlaEx =
    tla.assignPrime(tla.name(name), rhs)

  private def mkNotAssign(name: String, value: Int): TlaEx =
    tla.primeEq(tla.name(name), tla.int(value))

  private def mkNotAssign(name: String, rhs: TlaEx): TlaEx =
    tla.primeEq(tla.name(name), rhs)
}
