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
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfter, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestSeqModelChecker extends FunSuite with BeforeAndAfter {
  private var solver: RecordingSolverContext =
    RecordingSolverContext.createZ3(None, SolverConfig(debug = false, profile = false, 0))
  private var rewriter = new SymbStateRewriterImpl(solver, new ExprGradeStoreImpl)
  private val types = Map(
      "i" -> IntT1(),
      "I" -> SetT1(IntT1()),
      "b" -> BoolT1(),
      "Ob" -> OperT1(Seq(), BoolT1())
  )
  private val intTag: Typed[TlaType1] = Typed(IntT1())

  before {
    // initialize the model checker
    solver = RecordingSolverContext.createZ3(None, SolverConfig(debug = false, profile = false, 0))
    rewriter = new SymbStateRewriterImpl(solver, new ExprGradeStoreImpl)
  }

  private def mkModuleWithX(): TlaModule = {
    TlaModule("root", List(TlaVarDecl("x")(Typed(IntT1()))))
  }

  private def mkModuleWithXandY(): TlaModule = {
    TlaModule("root", List(TlaVarDecl("x")(intTag), TlaVarDecl("y")(intTag)))
  }

  test("Init + Inv => OK") {
    // x' <- 2
    val initTrans = List(mkAssign("x", 2))
    val nextTrans = List(mkAssign("x", 2))
    val notInv = gt(name("x") ? "i", int(10))
      .typed(types, "b")
    val inv = not(notInv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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
    val notInv = lt(name("x") ? "i", int(10))
      .typed(types, "b")
    val inv = not(notInv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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
    val initTrans = List(mkAssign("x", name("N") ? "i", IntT1()))
    val nextTrans = List(mkAssign("x", name("N") ? "i", IntT1()))
    val module = new TlaModule("root", List(TlaConstDecl("N")(intTag), TlaVarDecl("x")(intTag)))
    val notInv = lt(name("x") ? "i", int(10))
      .typed(types, "b")
    val inv = not(notInv).typed(types, "b")

    val checkerInput = new CheckerInput(module, initTrans, nextTrans, Some(cinit), CheckerInputVC(List((inv, notInv))))
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
    val initTrans = List(mkAssign("x", name("N") ? "i", IntT1()))
    val nextTrans = List(mkAssign("x", name("N") ? "i", IntT1()))
    val module = new TlaModule("root", List(TlaConstDecl("N")(intTag), TlaVarDecl("x")(intTag)))
    val notInv = lt(name("x") ? "i", int(10))
      .typed(types, "b")
    val inv = not(notInv).typed(types, "b")

    val checkerInput = new CheckerInput(module, initTrans, nextTrans, Some(cinit), CheckerInputVC(List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 0, new File("."), Map(), false)
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.Error == outcome)
  }

  test("Init, deadlock") {
    // x' <- 2 /\ x' <- 1
    val initTrans = List(and(mkAssign("x", 2), mkNotAssign("x", 1)).typed(BoolT1()))
    val nextTrans = List(mkAssign("x", 2))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
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
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
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
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
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
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x < 5
    val inv = lt(name("x") ? "i", int(5))
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x < 5
    val inv = lt(name("x") ? "i", int(5))
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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

  test("Init + Next x 10 + ActionInv (before + all-enabled) => ERR") {
    // x' := 2 \/ x' := 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x' < x
    val inv = lt(prime(name("x") ? "i") ? "i", name("x") ? "i")
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List(), List((inv, notInv))))
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

  test("Init + Next x 10 + ActionInv (before + all-enabled) => OK") {
    // x' := 2 \/ x' := 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x' > x
    val inv = gt(prime(name("x") ? "i") ? "i", name("x") ? "i")
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List(), List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    params.discardDisabled = false
    params.invariantMode = InvariantMode.BeforeJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next x 10 + Inv (after + all-enabled) => ERR") {
    // x' <- 2 \/ x' <- 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' <- x + 1
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x < 5
    val inv = lt(name("x") ? "i", int(5))
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x < 5
    val inv = lt(name("x") ? "i", int(5))
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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

  test("Init + Next x 10 + ActionInv (after + all-enabled) => ERR") {
    // x' := 2 \/ x' := 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x' < x
    val inv = lt(prime(name("x") ? "i") ? "i", name("x") ? "i")
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List(), List((inv, notInv))))
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

  test("Init + Next x 10 + ActionInv (after + all-enabled) => OK") {
    // x' := 2 \/ x' := 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x' > x
    val inv = gt(prime(name("x") ? "i") ? "i", name("x") ? "i")
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List(), List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    params.discardDisabled = false
    params.invariantMode = InvariantMode.AfterJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next x 10 + ActionInv (before) => ERR") {
    // x' := 2 \/ x' := 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x' < x
    val inv = lt(prime(name("x") ? "i") ? "i", name("x") ? "i")
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List(), List((inv, notInv))))
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

  test("Init + Next x 10 + ActionInv (before) => OK") {
    // x' := 2 \/ x' := 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x' > x
    val inv = gt(prime(name("x") ? "i") ? "i", name("x") ? "i")
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List(), List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    params.discardDisabled = true
    params.invariantMode = InvariantMode.BeforeJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next x 10 + ActionInv (after) => ERR") {
    // x' := 2 \/ x' := 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x' < x
    val inv = lt(prime(name("x") ? "i") ? "i", name("x") ? "i")
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List(), List((inv, notInv))))
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

  test("Init + Next x 10 + ActionInv (after) => OK") {
    // x' := 2 \/ x' := 1
    val initTrans = List(mkAssign("x", 2), mkAssign("x", 1))
    // x' := x + 1
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x' > x
    val inv = gt(prime(name("x") ? "i") ? "i", name("x") ? "i")
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List(), List((inv, notInv))))
    val params = new ModelCheckerParams(checkerInput, stepsBound = 10, new File("."), Map(), false)
    params.discardDisabled = true
    params.invariantMode = InvariantMode.AfterJoin
    // initialize the model checker
    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(params.consts, params.vars, ctx)
    val checker = new SeqModelChecker(params, checkerInput, trex)
    val outcome = checker.run()
    assert(Checker.Outcome.NoError == outcome)
  }

  test("Init + Next x 2 (LET-IN) + Inv => ERR") {
    // x' <- 1
    val initTrans = List(mkAssign("x", 1))
    // x' <- x + 1
    val assign = mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1())
    val nextTrans = List(assign)
    // x < 3
    val pred = lt(name("x") ? "i", int(3))
      .typed(types, "b")
    val letDef = letIn(appOp(name("Foo") ? "Ob") ? "b",
        declOp("Foo", pred)
          .typedOperDecl(types, "Ob"))
    val inv = letDef
      .typed(types, "b")
    val notInv = not(inv).typed(types, "b")

    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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
    val initTrans = List(and(mkAssign("y", 1), mkAssign("x", 1)).typed(BoolT1()))
    // y' <- y + 1 /\ x' <- x + 1
    val nextTrans = List(
        and(
            mkAssign("y", plus(name("y") ? "i", int(1)) ? "i", IntT1()),
            mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1())
        ).typed(BoolT1())) ///
    val inv = eql(
        eql(int(3), name("x") ? "i") ? "b",
        eql(int(3), name("y") ? "i") ? "b"
    ).typed(types, "b")
    val notInv = not(inv).typed(types, "b")

    val checkerInput =
      new CheckerInput(mkModuleWithXandY(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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
      List(and(gt(name("x") ? "i", int(3)) ? "b", mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1())).typed(
              types, "b"))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
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
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
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
      List(and(lt(name("x") ? "i", int(10)) ? "b", mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1())).typed(
              types, "b"))
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
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
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x < 100
    val inv = lt(name("x") ? "i", int(100))
      .typed(types, "b")
    val notInv = not(inv)
      .typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x /= 3
    val notInv = eql(name("x") ? "i", int(3))
      .typed(types, "b")
    val inv = not(notInv)
      .typed(BoolT1())
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x /= 3
    val notInv = eql(name("x") ? "i", int(3))
      .typed(types, "b")
    val inv = not(notInv)
      .typed(BoolT1())
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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
    val nextTrans = List(mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1()))
    // x < 5
    val inv = lt(name("x") ? "i", int(5))
      .typed(types, "b")
    val notInv = not(inv)
      .typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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
    val trans1 = mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1())
    val trans2 = and(gt(name("x") ? "i", int(100)) ? "b", mkAssign("x", name("x") ? "i", IntT1()))
      .typed(types, "b")
    val nextTrans = List(trans1, trans2)
    val checkerInput = new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC())
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
    val trans1 = mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1())
    val trans2 = and(gt(name("x") ? "i", int(10)) ? "b", mkAssign("x", name("x") ? "i", IntT1()))
      .typed(types, "b")
    val nextTrans = List(trans1, trans2)
    // ~(x <= 10)
    val notInv = gt(name("x") ? "i", int(10))
      .typed(types, "b")
    val inv = not(notInv)
      .typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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
    val trans1 = mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1())
    val trans2 = and(gt(name("x") ? "i", int(10)) ? "b", mkAssign("x", name("x") ? "i", IntT1()))
      .typed(types, "b")
    val nextTrans = List(trans1, trans2)
    // a constant initializer: \E t \in { 20, 10 }: N' \in {t}
    val cInit =
      apalacheSkolem(
          exists(
              name("t") ? "i",
              enumSet(int(20), int(10)) ? "I",
              mkAssign("N", name("t") ? "i", IntT1())
          ) ? "b")
        .typed(types, "b")

    // ~(x <= N)
    val notInv = gt(name("x") ? "i", name("N") ? "i")
      .typed(types, "b")
    val inv = not(notInv)
      .typed(types, "b")
    val dummyModule = new TlaModule("root", List(TlaConstDecl("N")(intTag), TlaVarDecl("x")(intTag)))
    val checkerInput =
      new CheckerInput(dummyModule, initTrans, nextTrans, Some(cInit), CheckerInputVC(List((inv, notInv))))
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
    val trans1 = mkAssign("x", plus(name("x") ? "i", int(1)) ? "i", IntT1())
    val trans2 = mkAssign("x", plus(name("x") ? "i", int(2)) ? "i", IntT1())
    val nextTrans = List(trans1, trans2)
    // ~(x <= 11)
    val notInv = gt(name("x") ? "i", int(11))
      .typed(types, "b")
    val inv = not(notInv)
      .typed(types, "b")
    val checkerInput =
      new CheckerInput(mkModuleWithX(), initTrans, nextTrans, None, CheckerInputVC(List((inv, notInv))))
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

  private def mkAssign(varName: String, value: Int): TlaEx = {
    assign(prime(name(varName) ? "i") ? "i", int(value))
      .typed(types, "b")
  }

  private def mkAssign(varName: String, rhs: BuilderEx, tt: TlaType1): TlaEx = {
    assign(prime(name(varName) ? "_tt") ? "_tt", rhs)
      .typed(types + ("_tt" -> tt), "b")
  }

  private def mkNotAssign(varName: String, value: Int): TlaEx = {
    eql(prime(name(varName) ? "i") ? "i", int(value) ? "i")
      .typed(types, "b")
  }

  private def mkNotAssign(varName: String, rhs: BuilderEx, tt: TlaType1): TlaEx = {
    eql(prime(name(varName) ? "_tt") ? "_tt", rhs)
      .typed(types + ("_tt" -> tt), "b")
  }
}
